/-
  `sl_block_auto` — automatic per-instruction spec lookup + macro
  composition.

  Surface tactic:

  - `sl_block_auto` — Read the goal's `CodeReq` literal (which must be
    a `union`-of-`singleton`s tree), dispatch each `(pc, insn)` pair to
    the appropriate per-instruction spec from `InstructionSpecs.lean`,
    and compose via the existing `SLBlockIter.slBlockIter` machinery.

    Replaces the per-step `have hi := xxx_spec ...` boilerplate plus
    `sl_block_iter [h0, h1, h2, ...]` pattern with a single tactic
    call.

    What gets auto-discharged:
    - `dst ≠ .r10` side conditions: the `dst` register is syntactically
      concrete from the `Insn` literal, so `mkDecideProof` evaluates
      the proposition at registration time.
    - `pcFree F` and `CodeReq.Disjoint cr1 cr2` subgoals — handled by
      `slBlockIter` exactly as in the manual `sl_block_iter` path.

    What stays visible to the user:
    - Value-bound side conditions like `v < 2 ^ 64` for `ldxh` / `ldxw`
      / `ldxdw`. The `v` mvar gets unified with a concrete `Nat` term
      by `slBlockIter`'s `extractFrame` / `isDefEq` pass, so the bound
      becomes (e.g.) `srcLam < 2 ^ 64` — the same hypothesis the user
      would pass manually.

  Dispatch is hand-coded per Insn ctor (`SVM/SBPF/SpecGen.lean::mkSpec`).
  Covered families:
  - 64-bit ALU imm + reg (mov / add / sub / mul / and / or / xor /
    lsh / rsh / arsh), `neg64`
  - 32-bit ALU imm + reg (same op set, result zero-extended), `neg32`
  - `lddw`, `ldx` (4 widths), `stx` (4 widths)

  Not covered:
  - `div` / `mod` (64- and 32-bit): specs carry a `divisor ≠ 0` side
    condition that the current `aluSpec` helper doesn't supply.
    Use `sl_block_iter` with a manual `have h := div64_imm_spec ...`.
  - Conditional jumps, `ja`, `exit`: non-linear; routed through
    `sl_branch` (the conditional-jump tactic) instead.
  - `call_local` / `callx`: call-stack triples pending a PartialState
    extension to track the call stack.

  Adding a new family is a single case in `mkSpec`.

  Future: replace the hand-dispatch with a `@[spec_gen]` attribute that
  parses each spec's type at registration time to derive the same
  metadata. Hand-dispatch is the fast initial deliverable.
-/

import Lean
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL

namespace SVM.SBPF
namespace SpecGen

open Lean Lean.Meta Lean.Elab.Tactic

/-- Spec application result: the built Expr (with mvars in value /
    side-condition positions) plus the list of side-condition mvars
    that should be exposed as user-visible residual goals once
    `slBlockIter` has resolved their parameter mvars via `isDefEq`. -/
structure SpecApp where
  app : Expr
  sideGoals : List MVarId
  deriving Inhabited

/-! ## Builders for fresh mvars / decidable proofs -/

private def mkNatMVar : MetaM Expr := do
  mkFreshExprMVar (Lean.Expr.const ``Nat [])

/-- Build a `dst ≠ SVM.SBPF.Reg.r10` proof by `decide` for a concrete
    `dst`. Requires `dst` to be syntactically a `Reg` constructor (it
    is, when extracted from a literal Insn). -/
private def mkNeqR10 (dst : Expr) : MetaM Expr := do
  let r10 : Expr := Lean.Expr.const ``SVM.SBPF.Reg.r10 []
  let prop ← mkAppM ``Ne #[dst, r10]
  mkDecideProof prop

/-- Build a fresh mvar of type `v < 2 ^ n` for a Nat-typed `v` and a
    concrete bound exponent `n`. Returns the mvar Expr (suitable to
    pass as the hyp arg) and its `MVarId` for later exposure. -/
private def mkBoundMVar (v : Expr) (n : Nat) : MetaM (Expr × MVarId) := do
  let two := mkNatLit 2
  let nLit := mkNatLit n
  let pow ← mkAppM ``HPow.hPow #[two, nLit]
  let prop ← mkAppM ``LT.lt #[v, pow]
  let m ← mkFreshExprMVar prop
  return (m, m.mvarId!)

/-! ## Per-Insn-family builders -/

/-- ALU op with `Src` operand (`.imm` or `.reg`). Pattern:
    `.<op> dst src`. The two-arity Insn ctor's args are
    `[dst, src]`; `src` is either `.imm imm` (use `immSpec`) or
    `.reg srcReg` (use `regSpec`). -/
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

/-- LDX. Pattern: `.ldx width dst src off`. Per-width side conds:
    `byte` has none (a single byte already fits in any `Nat` bound we
    care about); `half` requires `v < 2^16`; `word` `v < 2^32`;
    `dword` `v < 2^64`. -/
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

/-- 1-register negation (`.neg64 dst` / `.neg32 dst`). No Src arg —
    just `dst` plus the standard `dst ≠ .r10` side condition. -/
private def negSpec (pcLit dst : Expr) (specName : Name) : MetaM SpecApp := do
  let hne ← mkNeqR10 dst
  let vOld ← mkNatMVar
  let app ← mkAppM specName #[dst, vOld, pcLit, hne]
  return { app, sideGoals := [] }

/-- LDDW (`.lddw dst imm`). Two ctor args (`dst : Reg`, `imm : Int`) —
    not wrapped in a Src ctor. Spec signature mirrors `mov64_imm_spec`
    minus the `.imm` unwrap. -/
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

/-- ST (store-immediate). Pattern: `.st width baseReg off imm`. The clean
    `st{b,w,dw}_spec` wrappers discharge the step side condition
    internally (h_step is proved for the concrete `.st` shape), so — like
    STX — there are no residual side goals. There is no halfword variant
    (`sth_spec` / ST_H_IMM is unmodelled). -/
private def stSpec
    (pcLit w baseReg off imm : Expr) :
    MetaM SpecApp := do
  let baseAddr ← mkNatMVar
  let oldV ← mkNatMVar
  let specName ← match w.consumeMData.getAppFn.constName? with
    | some ``SVM.SBPF.Width.byte  => pure ``SVM.SBPF.stb_spec
    | some ``SVM.SBPF.Width.word  => pure ``SVM.SBPF.stw_spec
    | some ``SVM.SBPF.Width.dword => pure ``SVM.SBPF.stdw_spec
    | some ``SVM.SBPF.Width.half  =>
      throwError "SpecGen: ST_H_IMM (halfword store-immediate) has no spec (sth_spec is unmodelled)"
    | _ => throwError m!"SpecGen: unknown Width ctor in {w}"
  let app ← mkAppM specName #[baseReg, off, imm, baseAddr, oldV, pcLit]
  return { app, sideGoals := [] }

/-- Conditional-jump dispatch (imm-src variant). Builds the
    `<op>_imm_not_taken_spec` application — the linear form where the
    path hypothesis collapses the conditional to the fall-through PC
    (`pc + 1`). The hypothesis becomes a side mvar that `<;>
    assumption` discharges. `mkCondProp` builds the type of the path
    hypothesis from the (vDst, imm) pair — e.g. `vDst ≠ toU64 imm`
    for jeq, `vDst = toU64 imm` for jne. -/
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

/-! ## Top-level dispatcher -/

/-- Build the spec application for one `(pc, insn)` pair. Returns the
    application Expr with mvars in value / side-condition positions
    plus the list of `MVarId`s for side-conditions that should appear
    as user-visible residual goals. Throws if the Insn ctor has no
    registered dispatch (a small extension to add). -/
def mkSpec (pcLit : Expr) (insn : Expr) : MetaM SpecApp := do
  let insn := (← instantiateMVars insn).consumeMData
  let some ctor := insn.getAppFn.constName? |
    throwError m!"SpecGen.mkSpec: insn has no constant head: {insn}"
  let args := insn.getAppArgs
  match ctor with
  | ``SVM.SBPF.Insn.mov64  =>
    if h : args.size = 2 then
      aluSpec pcLit (args[0]'(by omega)) (args[1]'(by omega))
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
  -- div/mod (64- and 32-bit, imm + reg) intentionally NOT dispatched
  -- here: their specs carry an `hnz : divisor ≠ 0` side condition that
  -- the current `aluSpec` helper doesn't supply. Use `sl_block_iter`
  -- with a manual `have h := div64_imm_spec ... hnz` for now.
  -- 32-bit ALU (result zero-extended; spec signatures identical to 64-bit).
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
  -- Control flow. Conditional jumps dispatch to the linear "not
  -- taken" variants in InstructionSpecs/Jump.lean — the path
  -- hypothesis becomes a residual goal discharged by
  -- `<;> assumption` once `vDst` is unified by the chain.
  | ``SVM.SBPF.Insn.jeq =>
    condJumpImmSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jeq_imm_not_taken_spec
      (fun v i => do
        let u64 ← mkAppM ``SVM.SBPF.toU64 #[i]
        mkAppM ``Ne #[v, u64])
  | ``SVM.SBPF.Insn.jne =>
    condJumpImmSpec pcLit args[0]! args[1]! args[2]!
      ``SVM.SBPF.jne_imm_not_taken_spec
      (fun v i => do
        let u64 ← mkAppM ``SVM.SBPF.toU64 #[i]
        mkAppM ``Eq #[v, u64])
  | ``SVM.SBPF.Insn.ja =>
    jaSpec pcLit args[0]!
  -- call_local: take the target PC literal directly, then build
  -- `call_local_spec`. The five r6..r10 values + call stack get
  -- their own mvars; slBlockIter unifies them with whatever's in
  -- the chain's state at this point.
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
  -- exit: dispatch to `exit_pops_spec` (the nested-return case).
  -- The frame is constructed explicitly as `CallFrame.mk` with
  -- field-level mvars (rather than a single opaque frame mvar). When
  -- slBlockIter composes the chain, the frame this exit pops needs
  -- to unify with the frame pushed by the matching `call_local`'s
  -- post — which is itself constructed as `⟨pc+1, r6V, ...⟩`. With
  -- both sides as constructor applications, the unifier reduces the
  -- problem to field-wise Nat equalities (linear in the number of
  -- fields). With one side opaque (`frame : CallFrame`), the
  -- elaborator has to peel off `frame.retPc`, `frame.savedR6`, etc.
  -- via projection — that path triggers pathological recursion.
  -- Top-level exit (which terminates the program) is NOT in this
  -- chain — the qedlift walker stops before reaching it.
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

/-- Walk a `CodeReq` Expr — a `union`-of-`singleton`s tree, in any
    left/right grouping — and return `(pcExpr, insnExpr)` pairs in
    pc-order (left-to-right flatten). -/
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
      -- `slBlockIter` assigns the main goal + discharges pcFree /
      -- Disjoint side conds + calls `setGoals []`. After it returns,
      -- any side-cond mvars we collected that still aren't assigned
      -- become the residual user-visible goals.
      slBlockIter hyps
      let unsolved ← sideMvarIds.filterM (fun m => return !(← m.isAssigned))
      setGoals unsolved

end SVM.SBPF
