/-
  `sl_block_auto` — automatic per-instruction spec lookup + composition.

  Reads the goal's `CodeReq` literal (a `union`-of-`singleton`s tree),
  dispatches each `(pc, insn)` to the matching spec from
  `InstructionSpecs.lean`, composes via `SLBlockIter.slBlockIter`. Replaces
  the per-step `have hi := xxx_spec …` + `sl_block_iter [...]` boilerplate.

  Auto-discharged: `dst ≠ .r10` (concrete `dst` → `mkDecideProof`),
  `pcFree`/`Disjoint` (by `slBlockIter`). Stays user-visible: value bounds
  like `v < 2^64` for `ldxh`/`ldxw`/`ldxdw` (the `v` mvar is unified to a
  concrete term, so the bound matches what the user would pass manually).

  Dispatch is hand-coded per Insn ctor in `mkSpec`. Covered: 64/32-bit ALU
  imm+reg (mov/add/sub/mul/and/or/xor/lsh/rsh/arsh), neg64/neg32, lddw,
  ldx/stx (4 widths each). NOT covered (and why):
  - div/mod: specs carry a `divisor ≠ 0` side cond `aluSpec` can't supply
    — use `sl_block_iter` with a manual `have h := div64_imm_spec …`.
  - cond jumps / ja / exit: non-linear, routed through `sl_branch`.
  - call_local / callx: call-stack triples pending a PartialState extension.
-/

import Lean
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL

namespace SVM.SBPF
namespace SpecGen

open Lean Lean.Meta Lean.Elab.Tactic

/-- Spec application result: built Expr (mvars in value/side-cond slots)
    plus the side-cond mvars to expose as residual goals once `slBlockIter`
    has resolved their parameter mvars via `isDefEq`. -/
structure SpecApp where
  app : Expr
  sideGoals : List MVarId
  deriving Inhabited

/-! ## Builders for fresh mvars / decidable proofs -/

private def mkNatMVar : MetaM Expr := do
  mkFreshExprMVar (Lean.Expr.const ``Nat [])

/-- Prove `dst ≠ SVM.SBPF.Reg.r10` by `decide` for a concrete `dst`
    (a `Reg` ctor, as extracted from a literal Insn). -/
private def mkNeqR10 (dst : Expr) : MetaM Expr := do
  let r10 : Expr := Lean.Expr.const ``SVM.SBPF.Reg.r10 []
  let prop ← mkAppM ``Ne #[dst, r10]
  mkDecideProof prop

/-- Fresh mvar of type `v < 2 ^ n`. Returns the Expr (the hyp arg) and its
    `MVarId` for later exposure. -/
private def mkBoundMVar (v : Expr) (n : Nat) : MetaM (Expr × MVarId) := do
  let two := mkNatLit 2
  let nLit := mkNatLit n
  let pow ← mkAppM ``HPow.hPow #[two, nLit]
  let prop ← mkAppM ``LT.lt #[v, pow]
  let m ← mkFreshExprMVar prop
  return (m, m.mvarId!)

/-! ## Per-Insn-family builders -/

/-- ALU op `.<op> dst src`: `src` is `.imm imm` (→ `immSpec`) or
    `.reg srcReg` (→ `regSpec`). -/
private def aluSpec
    (pcLit dst src : Expr) (immSpec regSpec : Name) :
    MetaM SpecApp := do
  let hne ← mkNeqR10 dst
  let srcN := src.consumeMData
  let srcArgs := srcN.getAppArgs
  match srcN.getAppFn.constName? with
  | some ``SVM.SBPF.Src.imm =>
    let imm := srcArgs[0]!
    let vOld ← mkNatMVar
    let app ← mkAppM immSpec #[dst, imm, vOld, pcLit, hne]
    return { app, sideGoals := [] }
  | some ``SVM.SBPF.Src.reg =>
    let srcReg := srcArgs[0]!
    let vOld ← mkNatMVar
    let v ← mkNatMVar
    let app ← mkAppM regSpec #[dst, srcReg, vOld, v, pcLit, hne]
    return { app, sideGoals := [] }
  | _ =>
    throwError m!"SpecGen: unknown Src ctor in {src}"

/-- LDX `.ldx width dst src off`. Per-width value bound: byte none, half
    `v < 2^16`, word `v < 2^32`, dword `v < 2^64`. -/
private def ldxSpec
    (pcLit w dst src off : Expr) :
    MetaM SpecApp := do
  let hne ← mkNeqR10 dst
  let vOldDst ← mkNatMVar
  let baseAddr ← mkNatMVar
  let val ← mkNatMVar
  match w.consumeMData.getAppFn.constName? with
  | some ``SVM.SBPF.Width.byte =>
    let app ← mkAppM ``SVM.SBPF.ldxb_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne]
    return { app, sideGoals := [] }
  | some ``SVM.SBPF.Width.half =>
    let (hv, hvId) ← mkBoundMVar val 16
    let app ← mkAppM ``SVM.SBPF.ldxh_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne, hv]
    return { app, sideGoals := [hvId] }
  | some ``SVM.SBPF.Width.word =>
    let (hv, hvId) ← mkBoundMVar val 32
    let app ← mkAppM ``SVM.SBPF.ldxw_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne, hv]
    return { app, sideGoals := [hvId] }
  | some ``SVM.SBPF.Width.dword =>
    let (hv, hvId) ← mkBoundMVar val 64
    let app ← mkAppM ``SVM.SBPF.ldxdw_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne, hv]
    return { app, sideGoals := [hvId] }
  | _ =>
    throwError m!"SpecGen: unknown Width ctor in {w}"

/-- 1-register negation (`.neg64`/`.neg32 dst`): just `dst` + the standard
    `dst ≠ .r10` side cond. -/
private def negSpec (pcLit dst : Expr) (specName : Name) : MetaM SpecApp := do
  let hne ← mkNeqR10 dst
  let vOld ← mkNatMVar
  let app ← mkAppM specName #[dst, vOld, pcLit, hne]
  return { app, sideGoals := [] }

/-- LDDW `.lddw dst imm`: `imm : Int` not wrapped in a Src ctor. Spec
    mirrors `mov64_imm_spec` minus the `.imm` unwrap. -/
private def lddwSpec (pcLit dst imm : Expr) : MetaM SpecApp := do
  let hne ← mkNeqR10 dst
  let vOld ← mkNatMVar
  let app ← mkAppM ``SVM.SBPF.lddw_spec #[dst, imm, vOld, pcLit, hne]
  return { app, sideGoals := [] }

/-- STX. Pattern: `.stx width baseReg off valReg`. No side conds. -/
private def stxSpec
    (pcLit w baseReg off valReg : Expr) :
    MetaM SpecApp := do
  let baseAddr ← mkNatMVar
  let vSrc ← mkNatMVar
  let oldV ← mkNatMVar
  let specName ← match w.consumeMData.getAppFn.constName? with
    | some ``SVM.SBPF.Width.byte  => pure ``SVM.SBPF.stxb_spec
    | some ``SVM.SBPF.Width.half  => pure ``SVM.SBPF.stxh_spec
    | some ``SVM.SBPF.Width.word  => pure ``SVM.SBPF.stxw_spec
    | some ``SVM.SBPF.Width.dword => pure ``SVM.SBPF.stxdw_spec
    | _ => throwError m!"SpecGen: unknown Width ctor in {w}"
  let app ← mkAppM specName #[baseReg, valReg, off, baseAddr, vSrc, oldV, pcLit]
  return { app, sideGoals := [] }

/-- ST (store-immediate) `.st width baseReg off imm`. The `st{b,h,w,dw}_spec`
    wrappers prove h_step internally for the concrete `.st` shape, so (like
    STX) there are no residual side goals. -/
private def stSpec
    (pcLit w baseReg off imm : Expr) :
    MetaM SpecApp := do
  let baseAddr ← mkNatMVar
  let oldV ← mkNatMVar
  let specName ← match w.consumeMData.getAppFn.constName? with
    | some ``SVM.SBPF.Width.byte  => pure ``SVM.SBPF.stb_spec
    | some ``SVM.SBPF.Width.half  => pure ``SVM.SBPF.sth_spec
    | some ``SVM.SBPF.Width.word  => pure ``SVM.SBPF.stw_spec
    | some ``SVM.SBPF.Width.dword => pure ``SVM.SBPF.stdw_spec
    | _ => throwError m!"SpecGen: unknown Width ctor in {w}"
  let app ← mkAppM specName #[baseReg, off, imm, baseAddr, oldV, pcLit]
  return { app, sideGoals := [] }

/-- Conditional-jump dispatch (imm-src). Builds `<op>_imm_not_taken_spec`,
    the linear form where the path hyp collapses the branch to the
    fall-through PC (`pc+1`); the hyp becomes a side mvar `<;> assumption`
    discharges. `mkCondProp` builds the path-hyp type from `(vDst, imm)` —
    e.g. `vDst ≠ toU64 imm` for jeq, `=` for jne. -/
private def condJumpImmSpec
    (pcLit dst src tgt : Expr)
    (notTakenSpec : Name)
    (mkCondProp : Expr → Expr → MetaM Expr) :
    MetaM SpecApp := do
  let srcN := src.consumeMData
  let srcArgs := srcN.getAppArgs
  match srcN.getAppFn.constName? with
  | some ``SVM.SBPF.Src.imm =>
    let imm := srcArgs[0]!
    let vDst ← mkNatMVar
    let condProp ← mkCondProp vDst imm
    let h ← mkFreshExprMVar condProp
    let app ← mkAppM notTakenSpec #[dst, imm, vDst, pcLit, tgt, h]
    return { app, sideGoals := [h.mvarId!] }
  | _ =>
    throwError m!"SpecGen: conditional jump with non-.imm src is not yet supported"

/-- `ja target`: unconditional jump. No side conds; post-PC is the
    target. -/
private def jaSpec (pcLit tgt : Expr) : MetaM SpecApp := do
  let app ← mkAppM ``SVM.SBPF.ja_spec #[tgt, pcLit]
  return { app, sideGoals := [] }

/-- A fresh mvar typed as `spec`'s next explicit argument after `known`. -/
private def trailingHypMVar (spec : Name) (known : Array Expr) : MetaM Expr := do
  let ty ← whnf (← inferType (← mkAppM spec known))
  match ty with
  | .forallE _ dom _ _ => mkFreshExprMVar dom
  | _ => throwError m!"SpecGen: {spec} takes no hypothesis after {known.size} arguments"

/-- Apply `spec` to `known` and one trailing hypothesis argument, which is
    left as a fresh mvar and exposed as a side goal (a path hypothesis or a
    divisor bound, discharged by `<;> assumption` against the theorem's
    hypotheses). -/
private def hypSpec (spec : Name) (known : Array Expr) : MetaM SpecApp := do
  let h ← trailingHypMVar spec known
  return { app := mkApp (← mkAppM spec known) h, sideGoals := [h.mvarId!] }

/-- As `hypSpec`, but the trailing hypothesis is closed, literal `Decidable`
    fact (an immediate divisor's non-zeroness) proved by `decide` now. -/
private def decidedSpec (spec : Name) (known : Array Expr) : MetaM SpecApp := do
  let h ← trailingHypMVar spec known
  h.mvarId!.assign (← mkDecideProof (← instantiateMVars (← inferType h)))
  return { app := mkApp (← mkAppM spec known) h, sideGoals := [] }

/-- Split a `Src` into `(isImm, payload)`. -/
private def srcParts (src : Expr) : MetaM (Bool × Expr) := do
  let srcN := src.consumeMData
  match srcN.getAppFn.constName? with
  | some ``SVM.SBPF.Src.imm => return (true, srcN.getAppArgs[0]!)
  | some ``SVM.SBPF.Src.reg => return (false, srcN.getAppArgs[0]!)
  | _ => throwError m!"SpecGen: unexpected Src {src}"

/-- A conditional jump on the fall-through path: `immSpec`/`regSpec` are its
    `*_not_taken_spec` lemmas; the path hypothesis is the side goal. -/
private def notTakenJumpSpec (pcLit dst src tgt : Expr) (immSpec regSpec : Name) :
    MetaM SpecApp := do
  let (isImm, x) ← srcParts src
  let vDst ← mkNatMVar
  if isImm then
    hypSpec immSpec #[dst, x, vDst, pcLit, tgt]
  else
    hypSpec regSpec #[dst, x, vDst, ← mkNatMVar, pcLit, tgt]

/-- V3 JMP32 on the fall-through path. -/
private def jmp32NotTakenSpec (pcLit cond dst src tgt : Expr) : MetaM SpecApp := do
  let (isImm, x) ← srcParts src
  let vDst ← mkNatMVar
  if isImm then
    hypSpec ``SVM.SBPF.jmp32_imm_not_taken_spec #[cond, dst, x, vDst, pcLit, tgt]
  else
    hypSpec ``SVM.SBPF.jmp32_reg_not_taken_spec #[cond, dst, x, vDst, ← mkNatMVar, pcLit, tgt]

/-- Division/remainder: an immediate divisor's non-zeroness is decided; a
    register divisor's is a side goal (the lift's `hnz_<pc>` hypothesis). -/
private def divModSpec (pcLit dst src : Expr) (immSpec regSpec : Name) : MetaM SpecApp := do
  let (isImm, x) ← srcParts src
  let hne ← mkNeqR10 dst
  if isImm then
    decidedSpec immSpec #[dst, x, ← mkNatMVar, pcLit, hne]
  else
    hypSpec regSpec #[dst, x, ← mkNatMVar, ← mkNatMVar, pcLit, hne]

/-! ## Top-level dispatcher -/

/-- Spec application for one `(pc, insn)` pair: the Expr (mvars in
    value/side-cond slots) + side-cond `MVarId`s to surface as residual
    goals. Throws on an Insn ctor with no registered dispatch. -/
def mkSpec (pcLit : Expr) (insn : Expr) : MetaM SpecApp := do
  let insn := (← instantiateMVars insn).consumeMData
  let some ctor := insn.getAppFn.constName? |
    throwError m!"SpecGen.mkSpec: insn has no constant head: {insn}"
  let args := insn.getAppArgs
  match ctor with
  | ``SVM.SBPF.Insn.mov64  =>
    if h : args.size = 2 then
      let dst := args[0]'(by omega)
      let src := args[1]'(by omega)
      if src.getAppFn.constName? == some ``SVM.SBPF.Src.reg &&
          src.getAppArgs[0]! == dst then
        let hne ← mkNeqR10 dst
        let v ← mkNatMVar
        let app ← mkAppM ``SVM.SBPF.mov64_self_spec #[dst, v, pcLit, hne]
        return { app, sideGoals := [] }
      else
        aluSpec pcLit dst src
          ``SVM.SBPF.mov64_imm_spec ``SVM.SBPF.mov64_reg_spec
    else throwError m!"SpecGen: mov64 expected 2 args, got {args.size}"
  | ``SVM.SBPF.Insn.add64  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.add64_imm_spec ``SVM.SBPF.add64_reg_spec
  | ``SVM.SBPF.Insn.sub64  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.sub64_imm_spec ``SVM.SBPF.sub64_reg_spec
  | ``SVM.SBPF.Insn.mul64  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.mul64_imm_spec ``SVM.SBPF.mul64_reg_spec
  | ``SVM.SBPF.Insn.and64  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.and64_imm_spec ``SVM.SBPF.and64_reg_spec
  | ``SVM.SBPF.Insn.or64   =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.or64_imm_spec ``SVM.SBPF.or64_reg_spec
  | ``SVM.SBPF.Insn.xor64  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.xor64_imm_spec ``SVM.SBPF.xor64_reg_spec
  | ``SVM.SBPF.Insn.lsh64  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.lsh64_imm_spec ``SVM.SBPF.lsh64_reg_spec
  | ``SVM.SBPF.Insn.rsh64  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.rsh64_imm_spec ``SVM.SBPF.rsh64_reg_spec
  | ``SVM.SBPF.Insn.arsh64 =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.arsh64_imm_spec ``SVM.SBPF.arsh64_reg_spec
  | ``SVM.SBPF.Insn.neg64  =>
    negSpec pcLit args[0]! ``SVM.SBPF.neg64_spec
  -- div/mod NOT dispatched: their specs carry `hnz : divisor ≠ 0`, which
  -- `aluSpec` can't supply. Use `sl_block_iter` + manual `div64_imm_spec … hnz`.
  -- 32-bit ALU (result zero-extended; spec signatures match 64-bit).
  | ``SVM.SBPF.Insn.mov32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.mov32_imm_spec ``SVM.SBPF.mov32_reg_spec
  | ``SVM.SBPF.Insn.add32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.add32_imm_spec ``SVM.SBPF.add32_reg_spec
  | ``SVM.SBPF.Insn.sub32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.sub32_imm_spec ``SVM.SBPF.sub32_reg_spec
  | ``SVM.SBPF.Insn.mul32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.mul32_imm_spec ``SVM.SBPF.mul32_reg_spec
  | ``SVM.SBPF.Insn.and32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.and32_imm_spec ``SVM.SBPF.and32_reg_spec
  | ``SVM.SBPF.Insn.or32   =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.or32_imm_spec ``SVM.SBPF.or32_reg_spec
  | ``SVM.SBPF.Insn.xor32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.xor32_imm_spec ``SVM.SBPF.xor32_reg_spec
  | ``SVM.SBPF.Insn.lsh32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.lsh32_imm_spec ``SVM.SBPF.lsh32_reg_spec
  | ``SVM.SBPF.Insn.rsh32  =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.rsh32_imm_spec ``SVM.SBPF.rsh32_reg_spec
  | ``SVM.SBPF.Insn.arsh32 =>
    aluSpec pcLit args[0]! args[1]!
      ``SVM.SBPF.arsh32_imm_spec ``SVM.SBPF.arsh32_reg_spec
  | ``SVM.SBPF.Insn.neg32  =>
    negSpec pcLit args[0]! ``SVM.SBPF.neg32_spec
  -- Load 64-bit immediate (not wrapped in `Src`).
  | ``SVM.SBPF.Insn.lddw =>
    lddwSpec pcLit args[0]! args[1]!
  | ``SVM.SBPF.Insn.ldx =>
    ldxSpec pcLit args[0]! args[1]! args[2]! args[3]!
  | ``SVM.SBPF.Insn.stx =>
    stxSpec pcLit args[0]! args[1]! args[2]! args[3]!
  | ``SVM.SBPF.Insn.st =>
    stSpec pcLit args[0]! args[1]! args[2]! args[3]!
  -- Control flow. Cond jumps → linear "not taken" variants; the path hyp
  -- becomes a residual goal discharged by `<;> assumption` once the chain
  -- unifies `vDst`.
  | ``SVM.SBPF.Insn.jeq =>
    if (← srcParts args[1]!).1 = false then
      notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
        ``SVM.SBPF.jeq_reg_not_taken_spec ``SVM.SBPF.jeq_reg_not_taken_spec
    else
    condJumpImmSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jeq_imm_not_taken_spec
      (fun v i => do
        let u64 ← mkAppM ``SVM.SBPF.toU64 #[i]
        mkAppM ``Ne #[v, u64])
  | ``SVM.SBPF.Insn.jne =>
    if (← srcParts args[1]!).1 = false then
      notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
        ``SVM.SBPF.jne_reg_not_taken_spec ``SVM.SBPF.jne_reg_not_taken_spec
    else
    condJumpImmSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jne_imm_not_taken_spec
      (fun v i => do
        let u64 ← mkAppM ``SVM.SBPF.toU64 #[i]
        mkAppM ``Eq #[v, u64])
  | ``SVM.SBPF.Insn.jgt =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jgt_imm_not_taken_spec ``SVM.SBPF.jgt_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jge =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jge_imm_not_taken_spec ``SVM.SBPF.jge_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jlt =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jlt_imm_not_taken_spec ``SVM.SBPF.jlt_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jle =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jle_imm_not_taken_spec ``SVM.SBPF.jle_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jsgt =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jsgt_imm_not_taken_spec ``SVM.SBPF.jsgt_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jsge =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jsge_imm_not_taken_spec ``SVM.SBPF.jsge_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jslt =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jslt_imm_not_taken_spec ``SVM.SBPF.jslt_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jsle =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jsle_imm_not_taken_spec ``SVM.SBPF.jsle_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jset =>
    notTakenJumpSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jset_imm_not_taken_spec ``SVM.SBPF.jset_reg_not_taken_spec
  | ``SVM.SBPF.Insn.jmp32 =>
    jmp32NotTakenSpec pcLit args[0]! args[1]! args[2]! args[3]!
  | ``SVM.SBPF.Insn.div64 =>
    divModSpec pcLit args[0]! args[1]! ``SVM.SBPF.div64_imm_spec ``SVM.SBPF.div64_reg_spec
  | ``SVM.SBPF.Insn.mod64 =>
    divModSpec pcLit args[0]! args[1]! ``SVM.SBPF.mod64_imm_spec ``SVM.SBPF.mod64_reg_spec
  | ``SVM.SBPF.Insn.div32 =>
    divModSpec pcLit args[0]! args[1]! ``SVM.SBPF.div32_imm_spec ``SVM.SBPF.div32_reg_spec
  | ``SVM.SBPF.Insn.mod32 =>
    divModSpec pcLit args[0]! args[1]! ``SVM.SBPF.mod32_imm_spec ``SVM.SBPF.mod32_reg_spec
  | ``SVM.SBPF.Insn.endian =>
    let hne ← mkNeqR10 args[0]!
    let app ← mkAppM ``SVM.SBPF.endian_spec
      #[args[0]!, args[1]!, args[2]!, ← mkNatMVar, pcLit, hne]
    return { app, sideGoals := [] }
  | ``SVM.SBPF.Insn.ja =>
    jaSpec pcLit args[0]!
  -- call_local: target PC literal + `call_local_spec`. The r6..r10 values
  -- and call stack get mvars; slBlockIter unifies them with the chain state.
  | ``SVM.SBPF.Insn.call_local =>
    let target := args[0]!
    let cs ← mkFreshExprMVar (← mkAppM ``List #[Lean.Expr.const ``SVM.SBPF.CallFrame []])
    let r6V ← mkNatMVar
    let r7V ← mkNatMVar
    let r8V ← mkNatMVar
    let r9V ← mkNatMVar
    let r10V ← mkNatMVar
    let app ← mkAppM ``SVM.SBPF.call_local_spec
      #[target, cs, r6V, r7V, r8V, r9V, r10V, pcLit]
    return { app, sideGoals := [] }
  -- exit → `exit_pops_spec` (nested return). The popped frame is built as
  -- `CallFrame.mk` with field-level mvars, NOT an opaque `frame : CallFrame`:
  -- it must unify with the `⟨pc+1, r6V, …⟩` frame the matching `call_local`
  -- pushed, and ctor-vs-ctor reduces to field-wise Nat eqs (linear), whereas
  -- an opaque frame forces projection-peeling that recurses pathologically.
  -- Top-level (program-terminating) exit is NOT in this chain — the qedlift
  -- walker stops before it.
  | ``SVM.SBPF.Insn.exit =>
    let retPc    ← mkNatMVar
    let savedR6  ← mkNatMVar
    let savedR7  ← mkNatMVar
    let savedR8  ← mkNatMVar
    let savedR9  ← mkNatMVar
    let savedR10 ← mkNatMVar
    let frame ← mkAppM ``SVM.SBPF.CallFrame.mk
      #[retPc, savedR6, savedR7, savedR8, savedR9, savedR10]
    let cs ← mkFreshExprMVar (← mkAppM ``List #[Lean.Expr.const ``SVM.SBPF.CallFrame []])
    let r6V ← mkNatMVar
    let r7V ← mkNatMVar
    let r8V ← mkNatMVar
    let r9V ← mkNatMVar
    let r10V ← mkNatMVar
    let app ← mkAppM ``SVM.SBPF.exit_pops_spec
      #[frame, cs, r6V, r7V, r8V, r9V, r10V, pcLit]
    return { app, sideGoals := [] }
  | _ =>
    throwError m!"SpecGen.mkSpec: unsupported Insn ctor {ctor}; add a dispatch case in SVM/SBPF/SpecGen.lean"

/-- Flatten a `CodeReq` `union`-of-`singleton`s tree (any grouping) to
    `(pcExpr, insnExpr)` pairs in pc-order. -/
partial def walkCodeReq (cr : Expr) : MetaM (List (Expr × Expr)) := do
  let cr := (← instantiateMVars cr).consumeMData
  let args := cr.getAppArgs
  match cr.getAppFn.constName? with
  | some ``SVM.SBPF.CodeReq.singleton =>
    if args.size != 2 then
      throwError m!"SpecGen.walkCodeReq: singleton has unexpected arity {args.size}"
    return [(args[0]!, args[1]!)]
  | some ``SVM.SBPF.CodeReq.union =>
    if args.size != 2 then
      throwError m!"SpecGen.walkCodeReq: union has unexpected arity {args.size}"
    let left ← walkCodeReq args[0]!
    let right ← walkCodeReq args[1]!
    return left ++ right
  | _ =>
    throwError m!"SpecGen.walkCodeReq: CodeReq must be a union-of-singletons literal; got\n  {cr}"

end SpecGen

/-! ## `sl_block_auto` -/

syntax "sl_block_auto" : tactic

open Lean Lean.Meta Lean.Elab.Tactic SpecGen SLBlockIter in
elab_rules : tactic
  | `(tactic| sl_block_auto) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let some _ ← parseTripleType target |
        throwError m!"sl_block_auto: goal is not a cuTripleWithin[Mem]:\n  {target}"
      let cr ← getCr target
      let pcInsnList ← walkCodeReq cr
      let mut hyps : List Expr := []
      let mut sideMvarIds : List MVarId := []
      for (pcLit, insnLit) in pcInsnList do
        let specApp ← mkSpec pcLit insnLit
        hyps := hyps ++ [specApp.app]
        sideMvarIds := sideMvarIds ++ specApp.sideGoals
      -- `slBlockIter` assigns the main goal, discharges pcFree/Disjoint,
      -- and `setGoals []`. Our collected side-cond mvars still unassigned
      -- afterward become the residual user-visible goals.
      slBlockIter hyps
      let unsolved ← sideMvarIds.filterM (fun m => return !(← m.isAssigned))
      setGoals unsolved

end SVM.SBPF
