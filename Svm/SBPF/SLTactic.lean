/-
  Phase C — separation-logic tactic suite.

  Surface (4 tactics + 1 term macro):

  - `sl_disjoint_codereq` (macro_rules) — discharge `CodeReq.Disjoint`
    goals for a union-of-singletons via `Disjoint_union_left` + `decide`.
    Used as the auto-discharge for the disjointness subgoals collected
    by `sl_block_iter`'s composition steps.

  - `sl_pcfree` (elab) — discharge `(...).pcFree` goals built from
    atomic assertions (`emp`, `regIs`, `memByteIs`, the `memU{16,32,64}Is`
    flavours) joined by `**`. Elab-wrapped so the recursive
    `apply pcFree_sepConj <;> sl_pcfree` branch bails when the target
    still has unresolved metavariables (otherwise `apply` spuriously
    solves a `?F.pcFree` goal by setting `?F := ?A ** ?B` and loops).
    Used as the auto-discharge for the F.pcFree subgoals collected by
    `sl_block_iter`'s framing steps.

  - `sl_swap_first h` (term macro) — reshape `h`'s pre/post via
    `sepConj_swap_first_two` (swap the first two atoms of a 3-fold
    sepConj). Used to pre-align a spec's atom order to the surrounding
    macro state when its natural order differs (e.g. `stxb_spec`
    produces `baseReg ** valReg ** mem` but a macro composing it after
    a `ldxb` step holds the value-reg first). The frame-extractor in
    `sl_block_iter` only handles prefix / suffix atom alignment, so
    interleaved permutations need this hint.

  - `sl_block_iter [h1, h2, …, hn]` (full elab) — chain `n`
    per-instruction specs into a single triple. Walks left-to-right,
    syntactically extracts the frame `F_i` per step
    (state ≡ P_i ** F_i, prefix; or state ≡ F_i ** P_i, suffix), builds
    the framed step via `cuTripleWithin{,Mem}_frame_{right,left}`, then
    composes via the variant of `..._seq{,_pure_left,_pure_right}` that
    matches the (chain, step) pure/mem combination. The
    `_seq_pure_left/right` lemmas drop the trivial `True` `rr` factor a
    pure step would otherwise contribute, so the chain's `rr` is a
    left-folded `∧` of only the memory-side region requirements —
    matching the natural shape of user-written `rr_goal`. pcFree and
    Disjoint subgoals collected during the walk are dispatched via
    `sl_pcfree` and `sl_disjoint_codereq`.

    Works for arbitrary `n` (including the 3+ step direct compositions
    that the previous `macro_rules`-only `sl_block` couldn't handle:
    nested `by`-block elaboration order made the middle steps' frame
    `F` indeterminable at `isDefEq` time).

  Limitations of `sl_block_iter` — each requires the user to pre-shape
  the spec list:

  - The user's `goalPre` atoms must match each step's `P_i` either as a
    prefix or suffix of the right-spine. Interleaved permutations
    aren't handled; use `sl_swap_first` to pre-permute a spec.

  - `rr_goal` must be a left-folded `∧` of the memory steps' rr's in
    the same order they appear in the spec list.
-/

import Lean
import Svm.SBPF.CPSSpec
import Svm.SBPF.InstructionSpecs

namespace Svm.SBPF

/-! ## CodeReq disjointness discharge -/

syntax "sl_disjoint_codereq" : tactic

macro_rules
  | `(tactic| sl_disjoint_codereq) => `(tactic|
      first
      | (refine CodeReq.singleton_disjoint_singleton _ _ ?_
         decide)
      | (apply CodeReq.Disjoint_union_left
         · sl_disjoint_codereq
         · sl_disjoint_codereq))

private example :
    (CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).Disjoint
      (CodeReq.singleton 2 (.stx .byte .r1 0 .r2)) := by
  sl_disjoint_codereq

private example :
    (((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
       (CodeReq.singleton 1 (.add64 .r2 (.imm 1))))).Disjoint
      (CodeReq.singleton 2 (.stx .byte .r1 0 .r2)) := by
  sl_disjoint_codereq

/-! ## pcFree discharge -/

syntax "sl_pcfree_atom" : tactic

macro_rules
  | `(tactic| sl_pcfree_atom) => `(tactic|
      first
      | exact pcFree_emp
      | exact pcFree_regIs _ _
      | exact pcFree_memByteIs _ _
      | exact pcFree_memU16Is _ _
      | exact pcFree_memU32Is _ _
      | exact pcFree_memU64Is _ _
      | exact pcFree_memBytes32Is _ _
      | exact pcFree_memBytesIs _ _)

syntax "sl_pcfree" : tactic

open Lean Lean.Meta Lean.Elab.Tactic in
elab_rules : tactic
  | `(tactic| sl_pcfree) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      if target.hasExprMVar then
        throwError "sl_pcfree: target has unresolved metavariables; resolve F first"
      try
        evalTactic (← `(tactic| sl_pcfree_atom))
      catch _ =>
        evalTactic (← `(tactic| apply pcFree_sepConj <;> sl_pcfree))

/-! ## sl_swap_first — swap first two atoms of a 3-fold sepConj

Given `h : cuTripleWithinMem N e e' cr (A ** B ** R) (A' ** B' ** R') rr`,
produces `cuTripleWithinMem N e e' cr (B ** A ** R) (B' ** A' ** R') rr`.
Used to pre-align a spec's atom order before `sl_block_iter`. -/

macro "sl_swap_first " h:term : term =>
  `(cuTripleWithinMem_weaken
      (fun h_ps => (sepConj_swap_first_two h_ps).mp)
      (fun h_ps => (sepConj_swap_first_two h_ps).mp)
      (fun _ h_rr => h_rr) $h)

/-! ## sl_block_iter — full iterative block-composition elab -/

namespace SLBlockIter

open Lean Lean.Meta Lean.Elab.Tactic

/-- Components extracted from a `cuTripleWithin[Mem]` application
    type. -/
structure StepInfo where
  isMem : Bool
  hyp : Expr
  pre : Expr
  post : Expr
  deriving Inhabited

/-- Parse a `cuTripleWithin[Mem]` type. Returns the parsed shape or
    `none` if the type isn't a triple. Strips mdata; avoids `whnf` or
    `unfold` because both `cuTripleWithin` and `cuTripleWithinMem` are
    `def`s whose bodies reduce to `∀ R, …` (peering through them
    erases the head constant we dispatch on). -/
def parseTripleType (e : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  let e := (← instantiateMVars e).consumeMData
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Svm.SBPF.cuTripleWithin =>
    if args.size = 6 then return some (false, args[4]!, args[5]!)
    return none
  | some ``Svm.SBPF.cuTripleWithinMem =>
    if args.size = 7 then return some (true, args[4]!, args[5]!)
    return none
  | _ => return none

/-- Extract the `cr` (code-requirement) argument from a `cuTripleWithin[Mem]`
    application type. -/
def getCr (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Svm.SBPF.cuTripleWithin =>
    if args.size = 6 then return args[3]!
  | some ``Svm.SBPF.cuTripleWithinMem =>
    if args.size = 7 then return args[3]!
  | _ => pure ()
  throwError m!"sl_block_iter.getCr: expected cuTripleWithin[Mem] type, got\n  {e}"

/-- Recursively flatten a sepConj tree to its leaf atoms in left-to-right
    order. `A ** B ** C` yields `[A, B, C]`; left-folded `(A ** B) ** C`
    also yields `[A, B, C]`; atomic `X` yields `[X]`. Calls `Expr.eta`
    before each step so an eta-expanded assertion produced by
    `cuTripleWithinMem_weaken` over a lambda is seen through to its
    underlying `sepConj` head. Both subtrees are recursed so non-right-
    folded shapes (e.g. `(P ** Q) ** F` produced by a frame rule over a
    multi-atom `P`) still flatten to the correct atom list. -/
partial def flattenSepConj (e : Expr) : List Expr :=
  let e := e.consumeMData.eta
  if e.isAppOfArity ``Svm.SBPF.sepConj 2 then
    let args := e.getAppArgs
    flattenSepConj args[0]! ++ flattenSepConj args[1]!
  else
    [e]

/-- Build a right-folded sepConj from a non-empty list of atoms. -/
def rebuildSepConj : List Expr → MetaM Expr
  | [] => throwError "sl_block_iter.rebuildSepConj: empty atom list"
  | [a] => return a
  | a :: rest => do
    let tail ← rebuildSepConj rest
    mkAppM ``Svm.SBPF.sepConj #[a, tail]

/-- Build a pointwise iff `∀ h, e h ↔ (right-fold of flatten e) h`.
    Returns `none` if `e` is already right-folded (refl). Recursively
    descends the sepConj tree, applying `sepConj_assoc` at each left-
    grouped junction to pull the leftmost atom out, and lifting the
    recursive normalization of the tail via `sepConj_iff_congr_right`.
    Used after each frame application to keep `chain.pre`/`chain.post`
    in fully right-folded form so the iff terms produced by
    `buildPermuteIff` match the chain's Expr literally at the
    `reshape_*` call sites. The `none` short-circuit avoids wrapping
    chain with a no-op `reshape_pre`/`_post` when the chain side is
    already right-folded (e.g. after a single-atom-pre frame step). -/
partial def buildRightFoldIff (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData.eta
  if !e.isAppOfArity ``Svm.SBPF.sepConj 2 then
    -- Atomic: already right-folded.
    return none
  let args := e.getAppArgs
  let L := args[0]!
  let R := args[1]!
  if !L.isAppOfArity ``Svm.SBPF.sepConj 2 then
    -- L is atomic; only need to normalize R.
    match ← buildRightFoldIff R with
    | none => return none -- (L ** R) is already right-folded.
    | some iff_R =>
      return some (← mkAppM ``Svm.SBPF.sepConj_iff_congr_right #[L, iff_R])
  else
    -- L = (A ** L_rest); pull A out via sepConj_assoc, recurse on
    -- `(L_rest ** R)`. Termination: each level reduces the depth of
    -- the leftmost atom by 1.
    let L_args := L.getAppArgs
    let A := L_args[0]!
    let L_rest := L_args[1]!
    let assocIff ← mkAppOptM ``Svm.SBPF.sepConj_assoc
      #[some A, some L_rest, some R]
    let innerExpr ← mkAppM ``Svm.SBPF.sepConj #[L_rest, R]
    match ← buildRightFoldIff innerExpr with
    | none =>
      -- inner is right-folded; assocIff suffices.
      return some assocIff
    | some inner =>
      let liftedIff ← mkAppM ``Svm.SBPF.sepConj_iff_congr_right #[A, inner]
      let combined ← mkAppM ``Svm.SBPF.sepConj_iff_trans_pw #[assocIff, liftedIff]
      return some combined

/-! ## Pointwise-iff permutation construction

Given two `List Expr` of atoms over the same multiset (compared via
`isDefEq`), build a Lean term proving the pointwise iff between their
right-folded sepConjs. Used by `extractFrame`/`slBlockIter` to align
spec atoms with a running state whose atom order doesn't naturally
admit a prefix or suffix match. -/

/-- Build a pointwise iff `∀ h, (atoms folded) h ↔ (atoms with k,k+1 swapped, folded) h`.
    Requires `atoms.length ≥ k + 2`. Lifts the head swap (`sepConj_comm`
    if 2-atom tail, else `sepConj_swap_first_two`) by `k` applications of
    `sepConj_iff_congr_right` to push the swap deeper into the right
    spine. -/
def buildAdjacentSwapIff (atoms : List Expr) (k : Nat) : MetaM Expr := do
  let n := atoms.length
  unless k + 2 ≤ n do
    throwError m!"sl_block_iter.buildAdjacentSwapIff: k+2={k+2} > n={n}"
  let pAtom := atoms[k]!
  let qAtom := atoms[k+1]!
  -- Head swap: inner iff at the tail starting at position k.
  let headSwap ←
    if k + 2 == n then
      -- 2-atom tail: (a_k ** a_{k+1}) ↔ (a_{k+1} ** a_k)
      mkAppOptM ``Svm.SBPF.sepConj_comm #[some pAtom, some qAtom]
    else do
      -- 3+ atom tail: (a_k ** a_{k+1} ** rest) ↔ (a_{k+1} ** a_k ** rest)
      let restAtoms := atoms.drop (k + 2)
      let rExpr ← rebuildSepConj restAtoms
      mkAppOptM ``Svm.SBPF.sepConj_swap_first_two
        #[some pAtom, some qAtom, some rExpr]
  -- Lift `k` times: peel atoms[k-1], atoms[k-2], …, atoms[0].
  let mut inner := headSwap
  let mut i := k
  while i > 0 do
    i := i - 1
    let leftAtom := atoms[i]!
    inner ← mkAppM ``Svm.SBPF.sepConj_iff_congr_right #[leftAtom, inner]
  return inner

/-- Normalize an atom Expr's address subterm using a fixed set of
    common rewrites:
      `effectiveAddr base (Int.ofNat n) → base + n`
      `effectiveAddr base 0 → base` (subsumed by the above + Nat.add_zero)
    This collapses the syntactic gap between `stxdw_spec`-produced
    atoms (which use `effectiveAddr baseAddr off`) and macro/syscall
    spec atoms (which write `baseAddr + 8` or `baseAddr` directly).
    Walks via `Lean.Meta.transform`. -/
private def normalizeAtomExpr (e : Expr) : MetaM Expr :=
  Lean.Meta.transform e (post := fun e' => do
    let e'' := e'.consumeMData
    match e''.getAppFnArgs with
    | (``Svm.SBPF.Memory.effectiveAddr, #[base, off]) =>
      let off := off.consumeMData
      -- off = @OfNat.ofNat Int n _  →  literal-int Nat value n
      match off.getAppFnArgs with
      | (``OfNat.ofNat, #[_, n, _]) =>
        match n.nat? with
        | some 0 => return .done base
        | some k =>
          let nLit := mkNatLit k
          let res ← mkAppOptM ``HAdd.hAdd #[none, none, none, none, base, nLit]
          return .done res
        | none => return .continue
      | _ =>
        -- Already `Int.ofNat n` form?
        match off.getAppFnArgs with
        | (``Int.ofNat, #[n]) =>
          match n.nat? with
          | some 0 => return .done base
          | some k =>
            let nLit := mkNatLit k
            let res ← mkAppOptM ``HAdd.hAdd #[none, none, none, none, base, nLit]
            return .done res
          | none => return .continue
        | _ => return .continue
    | _ => return .continue)

/-- Atom equality. Structural-first (`==` → `eqv`), then normalize
    `effectiveAddr` forms via `normalizeAtomExpr` and retry `==`,
    finally fall back to `isDefEq`. The normalization step catches
    the specific `stxdw_spec` vs macro-spec address-form mismatch
    that triggered ~96K `Nat.rec` invocations per iter at iter 5 of
    the stack-macro composition. -/
private def atomEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if a.eqv b then return true
  let aN ← normalizeAtomExpr a
  let bN ← normalizeAtomExpr b
  if aN == bN then return true
  isDefEq a b

/-- Selection-sort `src` into `tgt`-prefix order. For each `i ∈ [0..|tgt|)`,
    finds `tgt[i]` in `src.drop i` (modulo `atomEq`) and bubbles it down
    to position `i` via a sequence of adjacent transpositions. Returns
    `none` if `tgt` is not a sub-multiset of `src`; else returns
    `(swaps, finalAtoms)` where `swaps` is the list of positions `k`
    indicating "swap positions `k` and `k+1` of the current state" in
    order, and `finalAtoms` is the resulting permuted atom list (with
    `tgt` as a prefix). -/
partial def bubbleSortToPrefix (src tgt : List Expr) :
    MetaM (Option (List Nat × List Expr)) := do
  if tgt.length > src.length then return none
  let mut work : Array Expr := src.toArray
  let mut swaps : List Nat := []
  for i in [0:tgt.length] do
    let target := tgt[i]!
    let mut found : Option Nat := none
    for j in [i:work.size] do
      if (← atomEq work[j]! target) then
        found := some j
        break
    match found with
    | none => return none
    | some j =>
      -- Bubble work[j] down to position i via adjacent swaps at
      -- (j-1, j), (j-2, j-1), …, (i, i+1).
      let mut p := j
      while p > i do
        let tmp := work[p - 1]!
        work := work.set! (p - 1) work[p]!
        work := work.set! p tmp
        swaps := (p - 1) :: swaps
        p := p - 1
  return some (swaps.reverse, work.toList)

/-- Build an iff `∀ h, (rebuildSepConj atoms) h ↔ (foldSepConj atoms_lit) h`
    where `atoms_lit` is the Lean `List Assertion` literal containing
    `atoms`. The iff "adds the trailing emp" — `foldSepConj` always
    emits `... ** emp`, while `rebuildSepConj` does not.

    Term depth: O(|atoms|) — one `congr_right` per atom + one
    `sepConj_emp_right_symm` at the singleton base. Compare to the
    old O(N²) chain.

    Singleton (`[a]`): produces `sepConj_emp_right_symm a`.
    Recursive (`a :: rest`): produces `sepConj_iff_congr_right a (recurse on rest)`.
    Empty: throws (callers ensure non-empty). -/
partial def buildRebuildToFoldIff : List Expr → MetaM Expr
  | [] => throwError "buildRebuildToFoldIff: empty atoms"
  | [a] => mkAppOptM ``Svm.SBPF.sepConj_emp_right_symm #[some a]
  | a :: rest => do
    let restIff ← buildRebuildToFoldIff rest
    mkAppM ``Svm.SBPF.sepConj_iff_congr_right #[a, restIff]

/-- Build the Lean `List Assertion` literal `[a₀, a₁, …, aₙ₋₁]` from
    a Lean `List Expr` of atoms. Each atom must be of type `Assertion`. -/
def mkAtomListLit (atoms : List Expr) : MetaM Expr := do
  let assertionType ← mkConstWithFreshMVarLevels ``Svm.SBPF.Assertion
  let nilExpr ← mkAppOptM ``List.nil #[some assertionType]
  let mut acc := nilExpr
  for a in atoms.reverse do
    acc ← mkAppOptM ``List.cons #[some assertionType, some a, some acc]
  return acc

/-- Build the Lean `List Nat` literal `[k₀, k₁, …, kₘ₋₁]`. -/
def mkNatListLit (ns : List Nat) : MetaM Expr := do
  let natType : Expr := mkConst ``Nat
  let nilExpr ← mkAppOptM ``List.nil #[some natType]
  let mut acc := nilExpr
  for k in ns.reverse do
    let kLit := mkNatLit k
    acc ← mkAppOptM ``List.cons #[some natType, some kLit, some acc]
  return acc

/-- Build the full pointwise iff `∀ h, (src folded) h ↔ (final folded) h`
    where `final = tgt ++ frame` is `src` permuted to put `tgt` first.
    Returns `none` if `tgt`'s atoms aren't a sub-multiset of `src`'s.
    On success returns `(maybeIff, frame, didPermute)` where
    `maybeIff = none` iff the permutation was the identity.

    The iff is composed left-to-right via `sepConj_iff_trans_pw` over
    `buildAdjacentSwapIff` outputs (one per bubble-sort swap). This
    produces an O(N²) term in worst case, but each swap iff stays
    bounded (no `applySwaps` reduction by Lean's kernel — which the
    list-based alternative was incurring at ~100× cost). -/
def buildPermuteIff (src tgt : List Expr) :
    MetaM (Option (Option Expr × List Expr × Bool)) := do
  match ← bubbleSortToPrefix src tgt with
  | none => return none
  | some (swaps, final) =>
    let frame := final.drop tgt.length
    if swaps.isEmpty then
      return some (none, frame, false)
    -- Compose swap iffs left-to-right via `sepConj_iff_trans_pw`.
    let mut curAtoms := src
    let firstSwap :: restSwaps := swaps
      | unreachable!  -- swaps nonempty, handled above
    let mut chainIff ← buildAdjacentSwapIff curAtoms firstSwap
    -- Update curAtoms by applying the first swap.
    do
      let k := firstSwap
      let a := curAtoms[k]!
      let b := curAtoms[k+1]!
      let head := curAtoms.take k
      let tail := curAtoms.drop (k + 2)
      curAtoms := head ++ [b, a] ++ tail
    for k in restSwaps do
      let stepIff ← buildAdjacentSwapIff curAtoms k
      chainIff ← mkAppM ``Svm.SBPF.sepConj_iff_trans_pw #[chainIff, stepIff]
      let a := curAtoms[k]!
      let b := curAtoms[k+1]!
      let head := curAtoms.take k
      let tail := curAtoms.drop (k + 2)
      curAtoms := head ++ [b, a] ++ tail
    return some (some chainIff, frame, true)

inductive FrameResult where
  | noFrame
  | right (F : Expr)
  | left (F : Expr)
  /-- A general permutation is needed before frame-extraction. The
      `reshapeIff` proves `∀ h, (state folded) h ↔ ((target ++ frame)
      folded) h`. `frameExpr` is the right-folded `frame` (atoms not in
      `target`, in the post-permutation order). After applying the iff
      via `weaken`, frame-extraction proceeds as a right-frame. -/
  | reshape (reshapeIff : Expr) (frameExpr : Option Expr)
  deriving Inhabited

/-- Try to strip `targetAtoms` as a prefix of `stateAtoms` (modulo
    `isDefEq`). Returns the remaining suffix on success. -/
def tryStripPrefix : List Expr → List Expr → MetaM (Option (List Expr))
  | sAtoms, [] => return some sAtoms
  | [], _ :: _ => return none
  | s :: sRest, t :: tRest => do
    if ← atomEq s t then tryStripPrefix sRest tRest else return none

/-- Try to strip `targetAtoms` as a suffix of `stateAtoms`. Returns the
    remaining prefix on success. -/
def tryStripSuffix (stateAtoms targetAtoms : List Expr) :
    MetaM (Option (List Expr)) := do
  if targetAtoms.length > stateAtoms.length then return none
  let n := stateAtoms.length - targetAtoms.length
  let prefixPart := stateAtoms.take n
  let suffixPart := stateAtoms.drop n
  let rec go : List Expr → List Expr → MetaM Bool
    | [], [] => return true
    | s :: sRest, t :: tRest => do
      if ← atomEq s t then go sRest tRest else return false
    | _, _ => return false
  if ← go suffixPart targetAtoms then return some prefixPart
  else return none

/-- Compute the frame so that `state ≡ target ** F` (right frame),
    `state ≡ F ** target` (left frame), `state ≡ target` (no frame), or
    `state ≡ (target ** F) modulo permutation` (reshape needed).
    Prefix/suffix paths are tried first as fast no-permute matches;
    permutation falls back when target atoms are interleaved with
    extra state atoms. -/
def extractFrame (state target : Expr) : MetaM FrameResult := do
  let stateAtoms := flattenSepConj state
  let targetAtoms := flattenSepConj target
  match ← tryStripPrefix stateAtoms targetAtoms with
  | some [] => return .noFrame
  | some leftover => return .right (← rebuildSepConj leftover)
  | none =>
    match ← tryStripSuffix stateAtoms targetAtoms with
    | some [] => return .noFrame
    | some leftover => return .left (← rebuildSepConj leftover)
    | none =>
      -- Fall back to general permutation. `buildPermuteIff` succeeds
      -- iff `targetAtoms` is a sub-multiset of `stateAtoms`.
      match ← buildPermuteIff stateAtoms targetAtoms with
      | none =>
        throwError m!"sl_block_iter.extractFrame: target atoms are not a sub-multiset of state atoms.\n  state atoms:  {stateAtoms.toArray}\n  target atoms: {targetAtoms.toArray}"
      | some (none, frame, _) =>
        -- This shouldn't happen given prefix already failed, but guard:
        if frame.isEmpty then return .noFrame
        return .right (← rebuildSepConj frame)
      | some (some iff, frame, _) =>
        let frameExpr ← if frame.isEmpty then pure none
          else some <$> rebuildSepConj frame
        return .reshape iff frameExpr

/-- Build the framed step. Pure steps stay pure; `composeSteps` picks
    `_seq_pure_left/right` to chain them with a memory neighbour
    without adding a trivial-True `rr` factor. Appends the F.pcFree
    mvar (if any) to `pcfreeGoals`. Handles the post-reshape cases:
    `.noFrame` / `.right` / `.left` only — `.reshape` is converted to
    `.right` (or `.noFrame`) by `slBlockIter` after applying the iff.
    -/
def buildFramedStep (info : StepInfo) (fr : FrameResult)
    (pcfreeGoals : IO.Ref (List MVarId)) :
    MetaM (Expr × Expr × Bool) := do
  let h := info.hyp
  let isMem := info.isMem
  match fr with
  | .noFrame => return (h, info.post, isMem)
  | .right F =>
    let pcfreeType ← mkAppOptM ``Svm.SBPF.Assertion.pcFree #[some F]
    let hF ← mkFreshExprMVar pcfreeType
    pcfreeGoals.modify (hF.mvarId! :: ·)
    -- Extract N, pc1, pc2, cr, P, Q (and rr for Mem) from h's type to
    -- skip mkAppM's implicit-arg inference work.
    let hType ← inferType h
    let hArgs := (← instantiateMVars hType).consumeMData.getAppArgs
    let N := hArgs[0]!; let pc1 := hArgs[1]!; let pc2 := hArgs[2]!
    let cr := hArgs[3]!; let P := hArgs[4]!; let Q := hArgs[5]!
    let framed ← if isMem then
        let rr := hArgs[6]!
        mkAppOptM ``Svm.SBPF.cuTripleWithinMem_frame_right
          #[some F, some hF, some N, some pc1, some pc2, some cr,
            some P, some Q, some rr, some h]
      else
        mkAppOptM ``Svm.SBPF.cuTripleWithin_frame_right
          #[some F, some hF, some N, some pc1, some pc2, some cr,
            some P, some Q, some h]
    let newPost ← mkAppOptM ``Svm.SBPF.sepConj #[some info.post, some F]
    return (framed, newPost, isMem)
  | .left F =>
    let pcfreeType ← mkAppOptM ``Svm.SBPF.Assertion.pcFree #[some F]
    let hF ← mkFreshExprMVar pcfreeType
    pcfreeGoals.modify (hF.mvarId! :: ·)
    let hType ← inferType h
    let hArgs := (← instantiateMVars hType).consumeMData.getAppArgs
    let N := hArgs[0]!; let pc1 := hArgs[1]!; let pc2 := hArgs[2]!
    let cr := hArgs[3]!; let P := hArgs[4]!; let Q := hArgs[5]!
    let framed ← if isMem then
        let rr := hArgs[6]!
        mkAppOptM ``Svm.SBPF.cuTripleWithinMem_frame_left
          #[some F, some hF, some N, some pc1, some pc2, some cr,
            some P, some Q, some rr, some h]
      else
        mkAppOptM ``Svm.SBPF.cuTripleWithin_frame_left
          #[some F, some hF, some N, some pc1, some pc2, some cr,
            some P, some Q, some h]
    let newPost ← mkAppOptM ``Svm.SBPF.sepConj #[some F, some info.post]
    return (framed, newPost, isMem)
  | .reshape .. =>
    throwError "sl_block_iter.buildFramedStep: .reshape should be lowered to .right / .noFrame before this call"

/-- Apply `cuTripleWithin{,Mem}_reshape_post` to chain so its post becomes
    `newPost`. Uses the pointwise iff `iff_post : ∀ h, chainPost h ↔
    newPost h`. Extracts N/pc1/pc2/cr/P/Q from `chain`'s type
    explicitly so `mkAppOptM` doesn't have to infer them. -/
def reshapeChainPost (chain : Expr) (chainIsMem : Bool) (iff_post : Expr) :
    MetaM Expr := do
  let chainType ← inferType chain
  let cArgs := (← instantiateMVars chainType).consumeMData.getAppArgs
  let N := cArgs[0]!; let pc1 := cArgs[1]!; let pc2 := cArgs[2]!
  let cr := cArgs[3]!; let P := cArgs[4]!; let Q := cArgs[5]!
  if chainIsMem then
    let rr := cArgs[6]!
    mkAppOptM ``Svm.SBPF.cuTripleWithinMem_reshape_post
      #[some N, some pc1, some pc2, some cr, some P, some Q, none, some rr,
        some iff_post, some chain]
  else
    mkAppOptM ``Svm.SBPF.cuTripleWithin_reshape_post
      #[some N, some pc1, some pc2, some cr, some P, some Q, none,
        some iff_post, some chain]

/-- Apply `cuTripleWithin{,Mem}_reshape_pre` to chain so its pre becomes
    `newPre`. Uses the pointwise iff `iff_pre : ∀ h, newPre h ↔ chainPre h`. -/
def reshapeChainPre (chain : Expr) (chainIsMem : Bool) (iff_pre : Expr) :
    MetaM Expr := do
  let chainType ← inferType chain
  let cArgs := (← instantiateMVars chainType).consumeMData.getAppArgs
  let N := cArgs[0]!; let pc1 := cArgs[1]!; let pc2 := cArgs[2]!
  let cr := cArgs[3]!; let P := cArgs[4]!; let Q := cArgs[5]!
  if chainIsMem then
    let rr := cArgs[6]!
    mkAppOptM ``Svm.SBPF.cuTripleWithinMem_reshape_pre
      #[some N, some pc1, some pc2, some cr, some P, none, some Q, some rr,
        some iff_pre, some chain]
  else
    mkAppOptM ``Svm.SBPF.cuTripleWithin_reshape_pre
      #[some N, some pc1, some pc2, some cr, some P, none, some Q,
        some iff_pre, some chain]

/-- Compose two consecutive (already framed) triples. Picks the lemma
    variant that preserves the memory side's `rr` (no trivial-True
    factor in the chain's rr).

    Uses `mkAppOptM` with all implicit args (N, pc, cr, P, Q, R, rr)
    extracted explicitly from `h1`/`h2`'s types, instead of letting
    `mkAppM` infer them. Inference walks the chain's `inferType`
    repeatedly — for a chain that grows in depth each iteration, this
    is O(depth × iter) wasted work and was the bottleneck in the
    stack-macro composition. Explicit extraction reads off the args
    in one pass and skips inference entirely.

    Layout: `cuTripleWithin N pc1 pc2 cr P Q` →
      args[0..5] = N, pc1, pc2, cr, P, Q.
    `cuTripleWithinMem N pc1 pc2 cr P Q rr` →
      args[0..6] = N, pc1, pc2, cr, P, Q, rr. -/
def composeSteps (h1 h2 : Expr) (isMem1 isMem2 : Bool)
    (disjGoals : IO.Ref (List MVarId)) : MetaM (Expr × Bool) := do
  let h1Type ← inferType h1
  let h2Type ← inferType h2
  let h1Args := (← instantiateMVars h1Type).consumeMData.getAppArgs
  let h2Args := (← instantiateMVars h2Type).consumeMData.getAppArgs
  let N1 := h1Args[0]!
  let pc1 := h1Args[1]!
  let pc2 := h1Args[2]!
  let cr1 := h1Args[3]!
  let P  := h1Args[4]!
  let Q  := h1Args[5]!
  let N2 := h2Args[0]!
  let pc3 := h2Args[2]!
  let cr2 := h2Args[3]!
  let R  := h2Args[5]!
  let disjType ← mkAppOptM ``Svm.SBPF.CodeReq.Disjoint #[some cr1, some cr2]
  let hd ← mkFreshExprMVar disjType
  disjGoals.modify (hd.mvarId! :: ·)
  match isMem1, isMem2 with
  | false, false =>
    let chained ← mkAppOptM ``Svm.SBPF.cuTripleWithin_seq
      #[some N1, some N2, some pc1, some pc2, some pc3, some cr1, some cr2,
        some hd, some P, some Q, some R, some h1, some h2]
    return (chained, false)
  | true, false =>
    let rr := h1Args[6]!
    let chained ← mkAppOptM ``Svm.SBPF.cuTripleWithinMem_seq_pure_right
      #[some N1, some N2, some pc1, some pc2, some pc3, some cr1, some cr2,
        some hd, some P, some Q, some R, some rr, some h1, some h2]
    return (chained, true)
  | false, true =>
    let rr := h2Args[6]!
    let chained ← mkAppOptM ``Svm.SBPF.cuTripleWithinMem_seq_pure_left
      #[some N1, some N2, some pc1, some pc2, some pc3, some cr1, some cr2,
        some hd, some P, some Q, some R, some rr, some h1, some h2]
    return (chained, true)
  | true, true =>
    let rr1 := h1Args[6]!
    let rr2 := h2Args[6]!
    let chained ← mkAppOptM ``Svm.SBPF.cuTripleWithinMem_seq
      #[some N1, some N2, some pc1, some pc2, some pc3, some cr1, some cr2,
        some hd, some P, some Q, some R, some rr1, some rr2, some h1, some h2]
    return (chained, true)

/-- Run `tac` on each subgoal mvar in turn; throw if any fails. -/
def dischargeGoals (mvars : List MVarId) (tac : TSyntax `tactic)
    (label : String) : TacticM Unit := do
  for mvarId in mvars do
    if !(← mvarId.isAssigned) then
      setGoals [mvarId]
      try evalTactic tac
      catch e =>
        throwError m!"sl_block_iter: {label} failed on residual subgoal:\n  {← instantiateMVars (← mvarId.getType)}\n  {e.toMessageData}"

/-- Right-normalize the `pre` and `post` of a triple expression so both
    become `rebuildSepConj (flatten _)`. Applied after each frame
    application to keep intermediate chain states in a canonical right-
    folded shape — needed because `frame_right F hF h` produces `(P ** F)`
    which is non-right-folded when `P` is multi-atom (e.g. memory specs
    like `ldxdw` whose pre / post own 3 atoms). Each side is wrapped
    only when `buildRightFoldIff` returns a non-refl iff; otherwise the
    chain is returned unchanged for that side. -/
def rightNormalizeChain (chain : Expr) (chainIsMem : Bool) : MetaM Expr := do
  let chainType ← inferType chain
  let some (_, chainPre, chainPost) ← parseTripleType chainType |
    throwError m!"sl_block_iter.rightNormalizeChain: not a triple type:\n  {chainType}"
  let chain' ← match ← buildRightFoldIff chainPre with
    | none => pure chain
    | some iff_pre => reshapeChainPre chain chainIsMem iff_pre
  match ← buildRightFoldIff chainPost with
  | none => pure chain'
  | some iff_post => reshapeChainPost chain' chainIsMem iff_post

/-- Bridge chain's pre/post atom order to the user-stated `goalPre` /
    `goalPost` shape. Both sides have the same atom multisets (by
    construction: each step's framing collected the unmatched atoms as
    the frame, and post atoms = pre atoms with the consumed atoms
    renamed). Each bridge uses `buildPermuteIff` over the atom lists. -/
def bridgeChainToGoal (chain : Expr) (chainIsMem : Bool)
    (goalPre goalPost : Expr) : MetaM Expr := do
  let chainType ← inferType chain
  let some (_, chainPre, chainPost) ← parseTripleType chainType |
    throwError "bridgeChainToGoal: chain not a triple"
  let chainPreAtoms := flattenSepConj chainPre
  let goalPreAtoms := flattenSepConj goalPre
  let chainPostAtoms := flattenSepConj chainPost
  let goalPostAtoms := flattenSepConj goalPost
  -- Bridge pre.
  let chain' ←
    match ← buildPermuteIff chainPreAtoms goalPreAtoms with
    | none =>
      throwError m!"sl_block_iter.bridgeChainToGoal: chain pre atoms aren't a permutation of goalPre atoms.\n  chain pre:  {chainPreAtoms.toArray}\n  goal pre:   {goalPreAtoms.toArray}"
    | some (none, frame, _) =>
      unless frame.isEmpty do
        throwError m!"sl_block_iter.bridgeChainToGoal: chain pre has extra atoms not in goalPre: {frame.toArray}"
      pure chain
    | some (some iff, frame, _) =>
      unless frame.isEmpty do
        throwError m!"sl_block_iter.bridgeChainToGoal: chain pre has extra atoms not in goalPre: {frame.toArray}"
      reshapeChainPre chain chainIsMem iff
  -- Bridge post.
  match ← buildPermuteIff chainPostAtoms goalPostAtoms with
  | none =>
    throwError m!"sl_block_iter.bridgeChainToGoal: chain post atoms aren't a permutation of goalPost atoms.\n  chain post: {chainPostAtoms.toArray}\n  goal post:  {goalPostAtoms.toArray}"
  | some (none, frame, _) =>
    unless frame.isEmpty do
      throwError m!"sl_block_iter.bridgeChainToGoal: chain post has extra atoms not in goalPost: {frame.toArray}"
    pure chain'
  | some (some iff, frame, _) =>
    unless frame.isEmpty do
      throwError m!"sl_block_iter.bridgeChainToGoal: chain post has extra atoms not in goalPost: {frame.toArray}"
    reshapeChainPost chain' chainIsMem iff

/-- Main elab body. Single-pass loop: for each step, extract the frame
    against the current state (possibly with permutation reshape on the
    chain), build the framed step, right-normalize it, compose with the
    chain. After the loop, bridge chain's pre / post to the user-stated
    `goalPre` / `goalPost` atom order, then assign the resulting term to
    the goal and discharge accumulated `pcFree` + `Disjoint` subgoals. -/
def slBlockIter (hExprs : List Expr) : TacticM Unit := withMainContext do
  if hExprs.isEmpty then
    throwError "sl_block_iter: empty hypothesis list"
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (goalIsMem, goalPre, goalPost) ← parseTripleType target |
    throwError m!"sl_block_iter: goal is not a cuTripleWithin[Mem]:\n  {target}"
  let pcfreeGoals ← IO.mkRef ([] : List MVarId)
  let disjGoals ← IO.mkRef ([] : List MVarId)
  -- Track chain expr + isMem flag. `none` means "no chain built yet".
  let mut chain : Option (Expr × Bool) := none
  -- `currentState` is the chain's current post (or `goalPre` on iter 0,
  -- which acts as the implicit chain.post against which step 0's pre is
  -- aligned). Always right-folded after the loop's first iteration.
  let mut currentState := goalPre
  for h in hExprs do
    let hType ← inferType h
    let some (stepIsMem, stepPre, stepPost) ← parseTripleType hType |
      throwError m!"sl_block_iter: hypothesis is not a cuTripleWithin[Mem]:\n  {hType}"
    let info : StepInfo := { isMem := stepIsMem, hyp := h, pre := stepPre, post := stepPost }
    let fr ← extractFrame currentState info.pre
    -- Apply reshape iff to the chain's post if the frame extraction
    -- required a permutation. On iter 0 there's no chain yet — the
    -- reshape would apply to "what becomes the framed step"; we defer
    -- by leaving `currentState` un-reshaped, and the final
    -- `bridgeChainToGoal` will adjust chain.pre back to goalPre.
    let (lowFr, didReshape) ← match fr with
      | .reshape iff frameOpt =>
        let newFrameResult : FrameResult := match frameOpt with
          | none => .noFrame
          | some F => .right F
        -- Apply reshape to chain if it exists.
        match chain with
        | some (chainExpr, chainIsMem) =>
          let chainExpr' ← reshapeChainPost chainExpr chainIsMem iff
          chain := some (chainExpr', chainIsMem)
          pure (newFrameResult, true)
        | none =>
          -- iter 0: defer to final bridge.
          pure (newFrameResult, true)
      | other => pure (other, false)
    -- Build framed step.
    let (framed, _newPost, framedIsMem) ←
      buildFramedStep info lowFr pcfreeGoals
    -- Right-normalize the framed step so its pre / post are right-folded.
    let framedNorm ← rightNormalizeChain framed framedIsMem
    -- Compose with chain (or set as the initial chain).
    let chainExpr' : Expr ← match chain with
      | none => pure framedNorm
      | some (chainExpr, chainIsMem) =>
        let (composed, _) ← composeSteps chainExpr framedNorm chainIsMem framedIsMem disjGoals
        pure composed
    let chainIsMem' := match chain with
      | none => framedIsMem
      | some (_, chainIsMem) => chainIsMem || framedIsMem
    chain := some (chainExpr', chainIsMem')
    -- Update currentState from chain's new post.
    let chainType ← inferType chainExpr'
    let some (_, _, newPost) ← parseTripleType chainType |
      throwError "sl_block_iter: chain type lost during composition"
    currentState := newPost
    -- Silence unused-warnings.
    let _ := didReshape
  let some (chainExpr, chainIsMem) := chain |
    throwError "sl_block_iter: no chain built"
  -- Lift the final chain to Mem if needed (all steps pure, goal Mem).
  let mut chainExpr := chainExpr
  let mut chainIsMem := chainIsMem
  if goalIsMem && !chainIsMem then
    chainExpr ← mkAppM ``Svm.SBPF.cuTripleWithin.toMem #[chainExpr]
    chainIsMem := true
  -- Bridge chain.pre / chain.post to goalPre / goalPost atom order.
  let bridged ← bridgeChainToGoal chainExpr chainIsMem goalPre goalPost
  -- Verify and assign.
  let bridgedType ← inferType bridged
  unless ← isDefEq target bridgedType do
    throwError m!"sl_block_iter: bridged chain type doesn't match goal.\n  goal:    {target}\n  chain:   {bridgedType}"
  goal.assign bridged
  -- Discharge side conditions.
  let pcfrees := (← pcfreeGoals.get).reverse
  let disjs := (← disjGoals.get).reverse
  dischargeGoals pcfrees (← `(tactic| sl_pcfree)) "sl_pcfree"
  dischargeGoals disjs (← `(tactic| sl_disjoint_codereq)) "sl_disjoint_codereq"
  setGoals []

end SLBlockIter

syntax "sl_block_iter" "[" term,* "]" : tactic

open Lean Lean.Elab.Tactic in
elab_rules : tactic
  | `(tactic| sl_block_iter [$hs,*]) => withMainContext do
      let hExprs ← hs.getElems.toList.mapM
        (fun h => Lean.Elab.Term.elabTermAndSynthesize h.raw none)
      SLBlockIter.slBlockIter hExprs

end Svm.SBPF
