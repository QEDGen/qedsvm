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

  Dispatch is hand-coded per Insn ctor (`Svm/SBPF/SpecGen.lean::mkSpec`)
  for the spec families currently used in `Macros.lean`:
  ALU imm + reg families (mov / add / sub / mul / and / or / xor /
  lsh / rsh / arsh, both 64-bit), `ldx` (4 widths), `stx` (4 widths).
  Adding a new family is a single case in `mkSpec`.

  Future: replace the hand-dispatch with a `@[spec_gen]` attribute that
  parses each spec's type at registration time to derive the same
  metadata. Hand-dispatch is the fast initial deliverable.
-/

import Lean
import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic

namespace Svm.SBPF
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

/-- Build a `dst ≠ Svm.SBPF.Reg.r10` proof by `decide` for a concrete
    `dst`. Requires `dst` to be syntactically a `Reg` constructor (it
    is, when extracted from a literal Insn). -/
private def mkNeqR10 (dst : Expr) : MetaM Expr := do
  let r10 : Expr := Lean.Expr.const ``Svm.SBPF.Reg.r10 []
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
  | some ``Svm.SBPF.Src.imm =>
    let imm := srcArgs[0]!
    let vOld ← mkNatMVar
    let app ← mkAppM immSpec #[dst, imm, vOld, pcLit, hne]
    return { app, sideGoals := [] }
  | some ``Svm.SBPF.Src.reg =>
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
  | some ``Svm.SBPF.Width.byte =>
    let app ← mkAppM ``Svm.SBPF.ldxb_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne]
    return { app, sideGoals := [] }
  | some ``Svm.SBPF.Width.half =>
    let (hv, hvId) ← mkBoundMVar val 16
    let app ← mkAppM ``Svm.SBPF.ldxh_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne, hv]
    return { app, sideGoals := [hvId] }
  | some ``Svm.SBPF.Width.word =>
    let (hv, hvId) ← mkBoundMVar val 32
    let app ← mkAppM ``Svm.SBPF.ldxw_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne, hv]
    return { app, sideGoals := [hvId] }
  | some ``Svm.SBPF.Width.dword =>
    let (hv, hvId) ← mkBoundMVar val 64
    let app ← mkAppM ``Svm.SBPF.ldxdw_spec
      #[dst, src, off, vOldDst, baseAddr, val, pcLit, hne, hv]
    return { app, sideGoals := [hvId] }
  | _ =>
    throwError m!"SpecGen: unknown Width ctor in {w}"

/-- STX. Pattern: `.stx width baseReg off valReg`. No side conds. -/
private def stxSpec
    (pcLit w baseReg off valReg : Expr) :
    MetaM SpecApp := do
  let baseAddr ← mkNatMVar
  let vSrc ← mkNatMVar
  let oldV ← mkNatMVar
  let specName ← match w.consumeMData.getAppFn.constName? with
    | some ``Svm.SBPF.Width.byte  => pure ``Svm.SBPF.stxb_spec
    | some ``Svm.SBPF.Width.half  => pure ``Svm.SBPF.stxh_spec
    | some ``Svm.SBPF.Width.word  => pure ``Svm.SBPF.stxw_spec
    | some ``Svm.SBPF.Width.dword => pure ``Svm.SBPF.stxdw_spec
    | _ => throwError m!"SpecGen: unknown Width ctor in {w}"
  let app ← mkAppM specName #[baseReg, valReg, off, baseAddr, vSrc, oldV, pcLit]
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
  | ``Svm.SBPF.Insn.mov64  =>
    if h : args.size = 2 then
      aluSpec pcLit (args[0]'(by omega)) (args[1]'(by omega))
        ``Svm.SBPF.mov64_imm_spec ``Svm.SBPF.mov64_reg_spec
    else throwError m!"SpecGen: mov64 expected 2 args, got {args.size}"
  | ``Svm.SBPF.Insn.add64  =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.add64_imm_spec ``Svm.SBPF.add64_reg_spec
  | ``Svm.SBPF.Insn.sub64  =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.sub64_imm_spec ``Svm.SBPF.sub64_reg_spec
  | ``Svm.SBPF.Insn.mul64  =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.mul64_imm_spec ``Svm.SBPF.mul64_reg_spec
  | ``Svm.SBPF.Insn.and64  =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.and64_imm_spec ``Svm.SBPF.and64_reg_spec
  | ``Svm.SBPF.Insn.or64   =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.or64_imm_spec ``Svm.SBPF.or64_reg_spec
  | ``Svm.SBPF.Insn.xor64  =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.xor64_imm_spec ``Svm.SBPF.xor64_reg_spec
  | ``Svm.SBPF.Insn.lsh64  =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.lsh64_imm_spec ``Svm.SBPF.lsh64_reg_spec
  | ``Svm.SBPF.Insn.rsh64  =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.rsh64_imm_spec ``Svm.SBPF.rsh64_reg_spec
  | ``Svm.SBPF.Insn.arsh64 =>
    aluSpec pcLit args[0]! args[1]!
      ``Svm.SBPF.arsh64_imm_spec ``Svm.SBPF.arsh64_reg_spec
  | ``Svm.SBPF.Insn.ldx =>
    ldxSpec pcLit args[0]! args[1]! args[2]! args[3]!
  | ``Svm.SBPF.Insn.stx =>
    stxSpec pcLit args[0]! args[1]! args[2]! args[3]!
  | _ =>
    throwError m!"SpecGen.mkSpec: unsupported Insn ctor {ctor}; add a dispatch case in Svm/SBPF/SpecGen.lean"

/-- Walk a `CodeReq` Expr — a `union`-of-`singleton`s tree, in any
    left/right grouping — and return `(pcExpr, insnExpr)` pairs in
    pc-order (left-to-right flatten). -/
partial def walkCodeReq (cr : Expr) : MetaM (List (Expr × Expr)) := do
  let cr := (← instantiateMVars cr).consumeMData
  let args := cr.getAppArgs
  match cr.getAppFn.constName? with
  | some ``Svm.SBPF.CodeReq.singleton =>
    if args.size != 2 then
      throwError m!"SpecGen.walkCodeReq: singleton has unexpected arity {args.size}"
    return [(args[0]!, args[1]!)]
  | some ``Svm.SBPF.CodeReq.union =>
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

end Svm.SBPF
