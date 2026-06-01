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
import SVM.SBPF.CPSSpec
import SVM.SBPF.InstructionSpecs

namespace SVM.SBPF

/-! ## CodeReq disjointness discharge -/

syntax "sl_disjoint_codereq" : tactic

macro_rules
  | `(tactic| sl_disjoint_codereq) => `(tactic|
      first
      | (refine CodeReq.singleton_disjoint_singleton _ _ ?_
         first | decide | omega)
      | (apply CodeReq.Disjoint_union_left
         · sl_disjoint_codereq
         · sl_disjoint_codereq)
      | (apply CodeReq.Disjoint_union_right
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
      | exact pcFree_memBytesIs _ _
      | exact pcFree_callStackIs _
      | exact pcFree_returnDataIs _)

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
  | some ``SVM.SBPF.cuTripleWithin =>
    if args.size = 7 then return some (false, args[5]!, args[6]!)
    return none
  | some ``SVM.SBPF.cuTripleWithinMem =>
    if args.size = 8 then return some (true, args[5]!, args[6]!)
    return none
  | _ => return none

/-- Extract the `cr` (code-requirement) argument from a `cuTripleWithin[Mem]`
    application type. -/
def getCr (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``SVM.SBPF.cuTripleWithin =>
    if args.size = 7 then return args[4]!
  | some ``SVM.SBPF.cuTripleWithinMem =>
    if args.size = 8 then return args[4]!
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
  if e.isAppOfArity ``SVM.SBPF.sepConj 2 then
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
    mkAppM ``SVM.SBPF.sepConj #[a, tail]

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
  if !e.isAppOfArity ``SVM.SBPF.sepConj 2 then
    -- Atomic: already right-folded.
    return none
  let args := e.getAppArgs
  let L := args[0]!
  let R := args[1]!
  if !L.isAppOfArity ``SVM.SBPF.sepConj 2 then
    -- L is atomic; only need to normalize R.
    match ← buildRightFoldIff R with
    | none => return none -- (L ** R) is already right-folded.
    | some iff_R =>
      return some (← mkAppM ``SVM.SBPF.sepConj_iff_congr_right #[L, iff_R])
  else
    -- L = (A ** L_rest); pull A out via sepConj_assoc, then recurse on the
    -- *whole* reassociated form `A ** (L_rest ** R)`. Recursing on the whole
    -- (rather than just `L_rest ** R` under a `congr_right A`) is what flattens
    -- a *compound* head `A` — e.g. the codec's expanded pubkey group
    -- `(c0 ** c1 ** c2 ** c3)` sitting as the head of `group ** rest`. Treating
    -- such an `A` atomically left it nested, diverging from `flattenSepConj`'s
    -- full flatten. Termination: each `assoc` lifts the leftmost atom one level,
    -- strictly reducing the left-spine `sepConj` depth.
    let L_args := L.getAppArgs
    let A := L_args[0]!
    let L_rest := L_args[1]!
    let assocIff ← mkAppOptM ``SVM.SBPF.sepConj_assoc
      #[some A, some L_rest, some R]
    let newExpr ← mkAppM ``SVM.SBPF.sepConj #[A, ← mkAppM ``SVM.SBPF.sepConj #[L_rest, R]]
    match ← buildRightFoldIff newExpr with
    | none =>
      -- `A ** (L_rest ** R)` is already right-folded; assocIff suffices.
      return some assocIff
    | some inner =>
      let combined ← mkAppM ``SVM.SBPF.sepConj_iff_trans_pw #[assocIff, inner]
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
      mkAppOptM ``SVM.SBPF.sepConj_comm #[some pAtom, some qAtom]
    else do
      -- 3+ atom tail: (a_k ** a_{k+1} ** rest) ↔ (a_{k+1} ** a_k ** rest)
      let restAtoms := atoms.drop (k + 2)
      let rExpr ← rebuildSepConj restAtoms
      mkAppOptM ``SVM.SBPF.sepConj_swap_first_two
        #[some pAtom, some qAtom, some rExpr]
  -- Lift `k` times: peel atoms[k-1], atoms[k-2], …, atoms[0].
  let mut inner := headSwap
  let mut i := k
  while i > 0 do
    i := i - 1
    let leftAtom := atoms[i]!
    inner ← mkAppM ``SVM.SBPF.sepConj_iff_congr_right #[leftAtom, inner]
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
    | (``SVM.SBPF.Memory.effectiveAddr, #[base, off]) =>
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
  | [a] => mkAppOptM ``SVM.SBPF.sepConj_emp_right_symm #[some a]
  | a :: rest => do
    let restIff ← buildRebuildToFoldIff rest
    mkAppM ``SVM.SBPF.sepConj_iff_congr_right #[a, restIff]

/-- Build the Lean `List Assertion` literal `[a₀, a₁, …, aₙ₋₁]` from
    a Lean `List Expr` of atoms. Each atom must be of type `Assertion`. -/
def mkAtomListLit (atoms : List Expr) : MetaM Expr := do
  let assertionType ← mkConstWithFreshMVarLevels ``SVM.SBPF.Assertion
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
      chainIff ← mkAppM ``SVM.SBPF.sepConj_iff_trans_pw #[chainIff, stepIff]
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
    MetaM (Expr × Bool) := do
  let h := info.hyp
  let isMem := info.isMem
  match fr with
  | .noFrame => return (h, isMem)
  | .right F =>
    let pcfreeType ← mkAppOptM ``SVM.SBPF.Assertion.pcFree #[some F]
    let hF ← mkFreshExprMVar pcfreeType
    pcfreeGoals.modify (hF.mvarId! :: ·)
    -- Extract N, M, pc1, pc2, cr, P, Q (and rr for Mem) from h's type to
    -- skip mkAppM's implicit-arg inference work.
    let hType ← inferType h
    let hArgs := (← instantiateMVars hType).consumeMData.getAppArgs
    let N := hArgs[0]!; let M := hArgs[1]!
    let pc1 := hArgs[2]!; let pc2 := hArgs[3]!
    let cr := hArgs[4]!; let P := hArgs[5]!; let Q := hArgs[6]!
    let framed ← if isMem then
        let rr := hArgs[7]!
        mkAppOptM ``SVM.SBPF.cuTripleWithinMem_frame_right
          #[some F, some hF, some N, some M, some pc1, some pc2, some cr,
            some P, some Q, some rr, some h]
      else
        mkAppOptM ``SVM.SBPF.cuTripleWithin_frame_right
          #[some F, some hF, some N, some M, some pc1, some pc2, some cr,
            some P, some Q, some h]
    return (framed, isMem)
  | .left F =>
    let pcfreeType ← mkAppOptM ``SVM.SBPF.Assertion.pcFree #[some F]
    let hF ← mkFreshExprMVar pcfreeType
    pcfreeGoals.modify (hF.mvarId! :: ·)
    let hType ← inferType h
    let hArgs := (← instantiateMVars hType).consumeMData.getAppArgs
    let N := hArgs[0]!; let M := hArgs[1]!
    let pc1 := hArgs[2]!; let pc2 := hArgs[3]!
    let cr := hArgs[4]!; let P := hArgs[5]!; let Q := hArgs[6]!
    let framed ← if isMem then
        let rr := hArgs[7]!
        mkAppOptM ``SVM.SBPF.cuTripleWithinMem_frame_left
          #[some F, some hF, some N, some M, some pc1, some pc2, some cr,
            some P, some Q, some rr, some h]
      else
        mkAppOptM ``SVM.SBPF.cuTripleWithin_frame_left
          #[some F, some hF, some N, some M, some pc1, some pc2, some cr,
            some P, some Q, some h]
    return (framed, isMem)
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
  let N := cArgs[0]!; let M := cArgs[1]!
  let pc1 := cArgs[2]!; let pc2 := cArgs[3]!
  let cr := cArgs[4]!; let P := cArgs[5]!; let Q := cArgs[6]!
  if chainIsMem then
    let rr := cArgs[7]!
    mkAppOptM ``SVM.SBPF.cuTripleWithinMem_reshape_post
      #[some N, some M, some pc1, some pc2, some cr, some P, some Q, none,
        some rr, some iff_post, some chain]
  else
    mkAppOptM ``SVM.SBPF.cuTripleWithin_reshape_post
      #[some N, some M, some pc1, some pc2, some cr, some P, some Q, none,
        some iff_post, some chain]

/-- Apply `cuTripleWithin{,Mem}_reshape_pre` to chain so its pre becomes
    `newPre`. Uses the pointwise iff `iff_pre : ∀ h, newPre h ↔ chainPre h`. -/
def reshapeChainPre (chain : Expr) (chainIsMem : Bool) (iff_pre : Expr) :
    MetaM Expr := do
  let chainType ← inferType chain
  let cArgs := (← instantiateMVars chainType).consumeMData.getAppArgs
  let N := cArgs[0]!; let M := cArgs[1]!
  let pc1 := cArgs[2]!; let pc2 := cArgs[3]!
  let cr := cArgs[4]!; let P := cArgs[5]!; let Q := cArgs[6]!
  if chainIsMem then
    let rr := cArgs[7]!
    mkAppOptM ``SVM.SBPF.cuTripleWithinMem_reshape_pre
      #[some N, some M, some pc1, some pc2, some cr, some P, none, some Q,
        some rr, some iff_pre, some chain]
  else
    mkAppOptM ``SVM.SBPF.cuTripleWithin_reshape_pre
      #[some N, some M, some pc1, some pc2, some cr, some P, none, some Q,
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
  -- New layout: cuTripleWithin N M pc1 pc2 cr P Q (Mem appends rr).
  let N1 := h1Args[0]!
  let M1 := h1Args[1]!
  let pc1 := h1Args[2]!
  let pc2 := h1Args[3]!
  let cr1 := h1Args[4]!
  let P  := h1Args[5]!
  let Q  := h1Args[6]!
  let N2 := h2Args[0]!
  let M2 := h2Args[1]!
  let pc3 := h2Args[3]!
  let cr2 := h2Args[4]!
  let R  := h2Args[6]!
  let disjType ← mkAppOptM ``SVM.SBPF.CodeReq.Disjoint #[some cr1, some cr2]
  let hd ← mkFreshExprMVar disjType
  disjGoals.modify (hd.mvarId! :: ·)
  match isMem1, isMem2 with
  | false, false =>
    let chained ← mkAppOptM ``SVM.SBPF.cuTripleWithin_seq
      #[some N1, some N2, some M1, some M2, some pc1, some pc2, some pc3,
        some cr1, some cr2, some hd, some P, some Q, some R, some h1, some h2]
    return (chained, false)
  | true, false =>
    let rr := h1Args[7]!
    let chained ← mkAppOptM ``SVM.SBPF.cuTripleWithinMem_seq_pure_right
      #[some N1, some N2, some M1, some M2, some pc1, some pc2, some pc3,
        some cr1, some cr2, some hd, some P, some Q, some R, some rr,
        some h1, some h2]
    return (chained, true)
  | false, true =>
    let rr := h2Args[7]!
    let chained ← mkAppOptM ``SVM.SBPF.cuTripleWithinMem_seq_pure_left
      #[some N1, some N2, some M1, some M2, some pc1, some pc2, some pc3,
        some cr1, some cr2, some hd, some P, some Q, some R, some rr,
        some h1, some h2]
    return (chained, true)
  | true, true =>
    let rr1 := h1Args[7]!
    let rr2 := h2Args[7]!
    let chained ← mkAppOptM ``SVM.SBPF.cuTripleWithinMem_seq
      #[some N1, some N2, some M1, some M2, some pc1, some pc2, some pc3,
        some cr1, some cr2, some hd, some P, some Q, some R, some rr1, some rr2,
        some h1, some h2]
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

/-- Build a proof of `F.pcFree` directly, in one structural pass over the
    `sepConj` tree — dispatching each leaf atom on its head constant to
    the matching `pcFree_<atom>` lemma (which takes the atom's own args).
    Replaces the `sl_pcfree` tactic's per-atom `first | exact …`
    backtracking (10 elaboration attempts × every atom × every growing
    frame = O(n²) and the dominant `sl_block_iter` cost); this is a
    single `mkAppM` per node, no backtracking, no tactic-framework
    overhead. -/
partial def provePcFree (f : Expr) : MetaM Expr := do
  let f := f.consumeMData
  match f.getAppFn.constName? with
  | some c =>
    if c == ``SVM.SBPF.sepConj then
      let args := f.getAppArgs
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      mkAppM ``SVM.SBPF.pcFree_sepConj #[← provePcFree a, ← provePcFree b]
    else
      -- Leaf atom `SVM.SBPF.<atom>`: apply `SVM.SBPF.pcFree_<atom>` to
      -- the atom's explicit args (e.g. regIs r v → pcFree_regIs r v).
      let lemmaName := Name.str c.getPrefix ("pcFree_" ++ c.getString!)
      mkAppM lemmaName f.getAppArgs
  | none => throwError m!"provePcFree: not an assertion atom:\n  {f}"

/-- Fast bulk discharge of the `F.pcFree` frame side-goals via
    `provePcFree`. Falls back to the `sl_pcfree` tactic on any atom shape
    `provePcFree` doesn't recognise. -/
def dischargePcFree (mvars : List MVarId) : TacticM Unit := do
  for mvarId in mvars do
    if !(← mvarId.isAssigned) then
      let ty := (← instantiateMVars (← mvarId.getType)).consumeMData
      match ty with
      | .app _ f =>
        try mvarId.assign (← provePcFree f)
        catch _ => setGoals [mvarId]; evalTactic (← `(tactic| sl_pcfree))
      | _ => setGoals [mvarId]; evalTactic (← `(tactic| sl_pcfree))

/-- Build a proof of `cr1.Disjoint cr2` directly, recursing over the
    `union`/`singleton` tree (`Disjoint_union_{left,right}` for unions,
    `singleton_disjoint_singleton` + a `decide` of `pc₁ ≠ pc₂` at the
    leaves). Replaces `sl_disjoint_codereq`'s `first | …` backtracking
    (O(k) per goal × n growing goals = O(n²), the dominant cost once
    pcFree is fast). -/
partial def proveDisjoint (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData; let b := b.consumeMData
  match a.getAppFn.constName? with
  | some ``SVM.SBPF.CodeReq.union =>
    let aa := a.getAppArgs
    mkAppM ``SVM.SBPF.CodeReq.Disjoint_union_left
      #[← proveDisjoint aa[aa.size - 2]! b, ← proveDisjoint aa[aa.size - 1]! b]
  | some ``SVM.SBPF.CodeReq.singleton =>
    match b.getAppFn.constName? with
    | some ``SVM.SBPF.CodeReq.union =>
      let bb := b.getAppArgs
      mkAppM ``SVM.SBPF.CodeReq.Disjoint_union_right
        #[← proveDisjoint a bb[bb.size - 2]!, ← proveDisjoint a bb[bb.size - 1]!]
    | some ``SVM.SBPF.CodeReq.singleton =>
      let aa := a.getAppArgs; let bb := b.getAppArgs
      let ne ← mkAppM ``Ne #[aa[aa.size - 2]!, bb[bb.size - 2]!]
      mkAppM ``SVM.SBPF.CodeReq.singleton_disjoint_singleton
        #[aa[aa.size - 1]!, bb[bb.size - 1]!, ← mkDecideProof ne]
    | _ => throwError m!"proveDisjoint: rhs not a CodeReq union/singleton:\n  {b}"
  | _ => throwError m!"proveDisjoint: lhs not a CodeReq union/singleton:\n  {a}"

/-- Fast bulk discharge of the `cr1.Disjoint cr2` side-goals via
    `proveDisjoint`; falls back to `sl_disjoint_codereq` on shapes it
    doesn't recognise. -/
def dischargeDisjoint (mvars : List MVarId) : TacticM Unit := do
  for mvarId in mvars do
    if !(← mvarId.isAssigned) then
      let ty := (← instantiateMVars (← mvarId.getType)).consumeMData
      let args := ty.getAppArgs
      if ty.isAppOf ``SVM.SBPF.CodeReq.Disjoint && args.size ≥ 2 then
        try mvarId.assign (← proveDisjoint args[args.size - 2]! args[args.size - 1]!)
        catch _ => setGoals [mvarId]; evalTactic (← `(tactic| sl_disjoint_codereq))
      else
        setGoals [mvarId]; evalTactic (← `(tactic| sl_disjoint_codereq))

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

/-- Detect a bare `SVM.SBPF.emp` assertion (used to identify
    `ja_spec`-style steps that can be auto-widened to the surrounding
    chain state). -/
def isEmpAssertion (e : Expr) : Bool :=
  (e.consumeMData).isConstOf ``SVM.SBPF.emp

/-- Build the chain expression from a step-hypothesis list and a
    starting state. Walks left-to-right: for each step, extract the
    frame against the current state (possibly with permutation reshape
    on the chain), build the framed step, right-normalize it, compose
    with the chain. Returns the composed chain term + isMem flag —
    leaves the goal alone, so callers (sl_block_iter, sl_branch) can
    bridge or assemble as they need. pcFree + Disjoint subgoals are
    appended to the IO.Refs for the caller to discharge.

    Auto-widens `emp/emp` step hypotheses (e.g. `ja_spec`) to use the
    current chain state via `cuTripleWithin_widen_emp`, so users don't
    have to hand-write the `frame_right + sepConj_emp_left` dance. -/
def buildChainExpr (startState : Expr) (hExprs : List Expr)
    (pcfreeGoals disjGoals : IO.Ref (List MVarId)) :
    MetaM (Expr × Bool) := do
  if hExprs.isEmpty then
    throwError "buildChainExpr: empty hypothesis list"
  let mut chain : Option (Expr × Bool) := none
  let mut currentState := startState
  for hOrig in hExprs do
    let mut h := hOrig
    let mut hType ← inferType h
    let some (stepIsMem, stepPre, stepPost) ← parseTripleType hType |
      throwError m!"buildChainExpr: hypothesis is not a cuTripleWithin[Mem]:\n  {hType}"
    -- Auto-widen `cuTripleWithin _ _ _ _ emp emp` steps to use the
    -- current chain state as their pre/post via `cuTripleWithin_widen_emp`.
    -- Avoids forcing the user to manually frame+strip-emp for the
    -- common `ja_spec`-shaped specs.
    let mut stepPre := stepPre
    let mut stepPost := stepPost
    if !stepIsMem && isEmpAssertion stepPre && isEmpAssertion stepPost then
      let pcfreeTy ← mkAppM ``SVM.SBPF.Assertion.pcFree #[currentState]
      let pcfreeMvar ← mkFreshExprMVar pcfreeTy
      pcfreeGoals.modify (pcfreeMvar.mvarId! :: ·)
      h ← mkAppM ``SVM.SBPF.cuTripleWithin_widen_emp #[currentState, pcfreeMvar, h]
      hType ← inferType h
      let some (_, widenedPre, widenedPost) ← parseTripleType hType |
        throwError "buildChainExpr: widen_emp lost triple shape"
      stepPre := widenedPre
      stepPost := widenedPost
    let info : StepInfo := { isMem := stepIsMem, hyp := h, pre := stepPre, post := stepPost }
    let fr ← extractFrame currentState info.pre
    let (lowFr, _didReshape) ← match fr with
      | .reshape iff frameOpt =>
        let newFrameResult : FrameResult := match frameOpt with
          | none => .noFrame
          | some F => .right F
        match chain with
        | some (chainExpr, chainIsMem) =>
          let chainExpr' ← reshapeChainPost chainExpr chainIsMem iff
          chain := some (chainExpr', chainIsMem)
          pure (newFrameResult, true)
        | none =>
          pure (newFrameResult, true)
      | other => pure (other, false)
    let (framed, framedIsMem) ←
      buildFramedStep info lowFr pcfreeGoals
    let framedNorm ← rightNormalizeChain framed framedIsMem
    let chainExpr' : Expr ← match chain with
      | none => pure framedNorm
      | some (chainExpr, chainIsMem) =>
        let (composed, _) ← composeSteps chainExpr framedNorm chainIsMem framedIsMem disjGoals
        pure composed
    let chainIsMem' := match chain with
      | none => framedIsMem
      | some (_, chainIsMem) => chainIsMem || framedIsMem
    chain := some (chainExpr', chainIsMem')
    let chainType ← inferType chainExpr'
    let some (_, _, newPost) ← parseTripleType chainType |
      throwError "buildChainExpr: chain type lost during composition"
    currentState := newPost
  let some result := chain |
    throwError "buildChainExpr: no chain built"
  return result

def slBlockIter (hExprs : List Expr) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (goalIsMem, goalPre, goalPost) ← parseTripleType target |
    throwError m!"sl_block_iter: goal is not a cuTripleWithin[Mem]:\n  {target}"
  let pcfreeGoals ← IO.mkRef ([] : List MVarId)
  let disjGoals ← IO.mkRef ([] : List MVarId)
  let (chainExpr, chainIsMem) ← buildChainExpr goalPre hExprs pcfreeGoals disjGoals
  -- Lift the final chain to Mem if needed (all steps pure, goal Mem).
  let mut chainExpr := chainExpr
  let mut chainIsMem := chainIsMem
  if goalIsMem && !chainIsMem then
    chainExpr ← mkAppM ``SVM.SBPF.cuTripleWithin.toMem #[chainExpr]
    chainIsMem := true
  -- Bridge chain.pre / chain.post to goalPre / goalPost atom order.
  let bridged₀ ← bridgeChainToGoal chainExpr chainIsMem goalPre goalPost
  let bridgedType₀ ← inferType bridged₀
  -- Coerce the chain's Nat bounds (nSteps, nCu, exit_) to the goal's
  -- closed-form ones. The chain's bounds are nested `(a + b)` from each
  -- `cuTripleWithin_seq` step; the goal usually carries the closed sum.
  -- `cuTripleWithin_cast` discharges each equality via `omega` / `rfl`.
  let cArgs := (← instantiateMVars bridgedType₀).consumeMData.getAppArgs
  let tArgs := (← instantiateMVars target).consumeMData.getAppArgs
  let expectedArity := if chainIsMem then 8 else 7
  let mut bridged := bridged₀
  if cArgs.size = expectedArity && tArgs.size = expectedArity then
    let cN := cArgs[0]!; let cM := cArgs[1]!; let cE := cArgs[3]!
    let tN := tArgs[0]!; let tM := tArgs[1]!; let tE := tArgs[3]!
    let hN ← mkFreshExprMVar (← mkEq cN tN)
    let hM ← mkFreshExprMVar (← mkEq cM tM)
    let hE ← mkFreshExprMVar (← mkEq cE tE)
    for mv in [hN.mvarId!, hM.mvarId!, hE.mvarId!] do
      try
        setGoals [mv]
        evalTactic (← `(tactic| first | rfl | omega))
      catch _ => pure ()
    let castName := if chainIsMem then ``SVM.SBPF.cuTripleWithinMem_cast
                    else ``SVM.SBPF.cuTripleWithin_cast
    bridged ← mkAppM castName #[hN, hM, hE, bridged₀]
  setGoals [goal]
  let bridgedType ← inferType bridged
  unless ← isDefEq target bridgedType do
    throwError m!"sl_block_iter: bridged chain type doesn't match goal.\n  goal:    {target}\n  chain:   {bridgedType}"
  goal.assign bridged
  let pcfrees := (← pcfreeGoals.get).reverse
  let disjs := (← disjGoals.get).reverse
  dischargePcFree pcfrees
  dischargeDisjoint disjs
  setGoals []

/-- Build the pointwise-iff type `∀ h, lhs h ↔ rhs h` from two `Assertion`s
    (`Assertion = PartialState → Prop`). -/
def mkPwIffType (lhs rhs : Expr) : MetaM Expr := do
  let dom ← match ← whnf (← inferType lhs) with
    | .forallE _ d _ _ => pure d
    | _ => throwError "mkPwIffType: assertion is not a pi type"
  withLocalDeclD `h dom fun h => do
    let body ← mkAppM ``Iff #[mkApp lhs h, mkApp rhs h]
    mkForallFVars #[h] body

/-- Bridge two pointwise-defeq, equal-length atom lists with a pointwise iff
    `∀ h, rebuild(as) h ↔ rebuild(bs) h`, ascribing each atom pair's defeq in
    isolation. This is the workhorse behind `sl_exact` matching atoms that are
    defeq but not syntactically equal (e.g. the lift's `effectiveAddr baseAddr
    160` vs an aggregation rewrite's `baseAddr + 160`): composing the match iff
    through one side then the other forces the kernel into a *single* `isDefEq`
    over the whole ~50-atom sepConj, which it bails on (returning a spurious type
    mismatch) at that scale even though every leaf is defeq. Hinting each pair
    separately keeps every `isDefEq` single-atom and cheap. Returns `none` when
    `as` and `bs` are already syntactically identical. -/
partial def buildDefeqBridge : List Expr → List Expr → MetaM (Option Expr)
  | [], [] => return none
  | [a], [b] =>
    if a == b then return none
    else do
      let refl ← mkAppOptM ``SVM.SBPF.sepConj_iff_refl #[some a]
      return some (← mkExpectedTypeHint refl (← mkPwIffType a b))
  | a :: as, b :: bs => do
    let ra ← rebuildSepConj (a :: as)
    let rb ← rebuildSepConj (b :: bs)
    match ← buildDefeqBridge as bs with
    | none =>
      -- Tails syntactically identical; only the head may differ.
      if a == b then return none
      else do
        let refl ← mkAppOptM ``SVM.SBPF.sepConj_iff_refl #[some ra]
        return some (← mkExpectedTypeHint refl (← mkPwIffType ra rb))
    | some tail =>
      -- `congr_right` keeps the head fixed: (a ** rebuild as) ↔ (a ** rebuild bs).
      -- Ascribe the head a → b afterward (a single-atom defeq check).
      let cr ← mkAppM ``SVM.SBPF.sepConj_iff_congr_right #[a, tail]
      if a == b then return some cr
      else return some (← mkExpectedTypeHint cr (← mkPwIffType ra rb))
  | _, _ => throwError "buildDefeqBridge: atom lists differ in length"

end SLBlockIter

/-- `sl_block_iter [h₁, …]` composes the per-instruction specs into the
goal triple. The optional `generalizing [e₁, …]` clause abstracts each
listed value expression to a fresh opaque variable (`generalize … at *`)
BEFORE composition — complex bit-level values (wrapAdd/shift/mod chains)
carry no proof content of their own (the per-opcode spec already proved
what each computes), so threading them as opaque Nats keeps the
mechanical composition from re-reducing arithmetic via `whnf` at every
step. This is the dominant cost on long arms; abstracting it took
`PTokenTransferChecked` from a >15-minute timeout to closing. The
theorem statement is unaffected (generalize only touches the proof
goal); the bridge `e = v` stays in scope for the refinement layer. -/
syntax "sl_block_iter" "[" term,* "]" (" generalizing" " [" term,* "]")? : tactic

open Lean Lean.Elab.Tactic in
elab_rules : tactic
  | `(tactic| sl_block_iter [$hs,*] $[generalizing [$gs,*]]?) => withMainContext do
      -- Value-abstraction pre-pass: opaque-ify each listed value at the
      -- goal and every hypothesis (so the chain and goal stay aligned).
      if let some gs := gs then
        for g in gs.getElems do
          let v := mkIdent (← mkFreshUserName `vgen)
          let h := mkIdent (← mkFreshUserName `hgen)
          evalTactic (← `(tactic| generalize $h : $g = $v at *))
      -- Re-enter context (generalize rewrote the have-hypotheses) and
      -- compose. The have names are stable across generalize.
      withMainContext do
        let hExprs ← hs.getElems.toList.mapM
          (fun h => Lean.Elab.Term.elabTermAndSynthesize h.raw none)
        SLBlockIter.slBlockIter hExprs

/-! ## sl_branch — branch + join + post-distribute combinator

`sl_branch h_br [h_T₁, h_T₂, …] [h_F₁, h_F₂, …]` discharges a
`cuTripleWithin N pc₀ pcJoin cr P Q` goal by composing:

- `h_br` — a pre-framed `cuTripleWithinBranch` triple at `pc₀` that
  the user has already widened to the macro's full state via
  `cuTripleWithinBranch_frame_{left,right}`. Its `cond` is extracted
  from the type and threaded into the post-distribute step.
- `[h_T,*]` — step hypotheses for the true branch, in the format
  `sl_block_iter` accepts. The branch chain is built by reusing
  `sl_block_iter` directly.
- `[h_F,*]` — same for the false branch.

Internally emits one tactic block:

```
refine cuTripleWithin_weaken (fun _ x => x) ?_post
  (cuTripleWithinBranch_join ?disjBT ?disjBF ?disjTF h_br ?hT ?hF)
case hT => sl_block_iter [h_T,*]
case hF => sl_block_iter [h_F,*]
case disjBT => sl_disjoint_codereq
case disjBF => sl_disjoint_codereq
case disjTF => sl_disjoint_codereq
case _post =>
  intro _hp _hpost
  by_cases _hc : <cond>
  · simp only [_hc, if_true]  at _hpost ⊢; exact _hpost
  · simp only [_hc, if_false] at _hpost ⊢; exact _hpost
```

Source order matters: the chain cases run first, filling the `crT` /
`crF` metas, so `sl_disjoint_codereq`'s `decide` sees concrete code
requirements.

Limitations (matching `sl_block_iter`'s):

- The user's goal `cr` must be `((crBr ∪ crT_chain) ∪ crF_chain)` in
  the left-folded shape `cuTripleWithinBranch_join` produces.
- The goal `N` must equal `N0_h_br + max NT_chain NF_chain`.
- The goal `P` must equal `h_br`'s pre.
- The post-distribute `simp only [_hc, if_*]` finisher assumes the
  goal post mentions `cond` only inside `if … then … else …` terms
  with both branches having the same surrounding shape (the natural
  case — `r0 ↦ᵣ (if cond then a else b)`-style atoms). If the
  shapes diverge, fall back to a manual `weaken + by_cases`. -/

namespace SLBranch
open Lean Lean.Meta Lean.Elab.Tactic Lean.Elab.Term

/-- Parsed shape of a `cuTripleWithinBranch` application type.
    Layout matches the declaration:
    `cuTripleWithinBranch nSteps entry exitT exitF cond [Dec] cr P Q`. -/
structure BranchInfo where
  cond : Expr
  Q : Expr
  deriving Inhabited

def parseBranchType (brType : Expr) : MetaM BranchInfo := do
  let brType := (← instantiateMVars brType).consumeMData
  let args := brType.getAppArgs
  match brType.getAppFn.constName? with
  | some ``SVM.SBPF.cuTripleWithinBranch =>
    if args.size = 10 then
      return { cond := args[5]!, Q := args[9]! }
    throwError m!"sl_branch: cuTripleWithinBranch application has {args.size} args, expected 10"
  | _ =>
    throwError m!"sl_branch: h_br is not a cuTripleWithinBranch application:\n  {brType}"

end SLBranch

syntax "sl_branch" term:max "[" term,* "]" "[" term,* "]" : tactic

open Lean Lean.Elab.Tactic Lean.Elab.Term Lean.Meta SLBlockIter in
elab_rules : tactic
  | `(tactic| sl_branch $hBr [$tSteps,*] [$fSteps,*]) => withMainContext do
      let hBrExpr ← elabTermAndSynthesize hBr none
      let hBrType ← inferType hBrExpr
      let brInfo ← SLBranch.parseBranchType hBrType
      let condStx ← Lean.PrettyPrinter.delab brInfo.cond
      -- Build each branch chain into a concrete term against `brInfo.Q`
      -- (the join's intermediate `Q`). Pre-building avoids the
      -- application-order trap where `refine cuTripleWithinBranch_join`
      -- with chain-meta arguments leaves `1 + max ?NT ?NF` unreduced.
      let pcfreeGoals ← IO.mkRef ([] : List MVarId)
      let disjGoals ← IO.mkRef ([] : List MVarId)
      let tStepExprs ← tSteps.getElems.toList.mapM
        (fun s => elabTermAndSynthesize s.raw none)
      let fStepExprs ← fSteps.getElems.toList.mapM
        (fun s => elabTermAndSynthesize s.raw none)
      let (hTExpr, _) ← buildChainExpr brInfo.Q tStepExprs pcfreeGoals disjGoals
      let (hFExpr, _) ← buildChainExpr brInfo.Q fStepExprs pcfreeGoals disjGoals
      -- Assemble the join term with the chains concrete and disjointness
      -- as fresh metas. `mkAppM` unifies the cond/cr/N args naturally.
      let mkDisjMvar (a b : Expr) : MetaM Expr := do
        mkFreshExprMVar (← mkAppM ``SVM.SBPF.CodeReq.Disjoint #[a, b])
      let hBrArgs := ((← instantiateMVars hBrType).consumeMData).getAppArgs
      let crBr := hBrArgs[7]!
      let crT := (((← instantiateMVars (← inferType hTExpr))).consumeMData).getAppArgs[4]!
      let crF := (((← instantiateMVars (← inferType hFExpr))).consumeMData).getAppArgs[4]!
      let disjBT ← mkDisjMvar crBr crT
      let disjBF ← mkDisjMvar crBr crF
      let disjTF ← mkDisjMvar crT crF
      let joinExpr ← mkAppM ``SVM.SBPF.cuTripleWithinBranch_join
        #[disjBT, disjBF, disjTF, hBrExpr, hTExpr, hFExpr]
      let joinType ← inferType joinExpr
      -- Wrap in `cuTripleWithin_weaken` so the goal post can be in
      -- atom-distributed `(r ↦ᵣ if cond then a else b)` form rather
      -- than the join's natural `if cond then (r ↦ᵣ a) else (r ↦ᵣ b)`.
      -- Splice the join term in by asserting it as a local hypothesis
      -- first — delab'ing an Expr with metavariables loses the meta
      -- references and triggers fresh elaboration, which fails. The
      -- assert keeps the disjointness metas in `joinExpr` referable
      -- so they can be discharged after the refine.
      let mainGoal ← getMainGoal
      let asserted ← mainGoal.assert `_h_joined joinType joinExpr
      let (joinedFVar, postIntro) ← asserted.intro1
      replaceMainGoal [postIntro]
      let joinedIdent := mkIdent (← postIntro.withContext do
        pure (← FVarId.getDecl joinedFVar).userName)
      evalTactic (← `(tactic|
        refine cuTripleWithin_weaken (fun _ x => x) ?branchPost $joinedIdent))
      evalTactic (← `(tactic|
        case branchPost =>
          intro _hp _hpost
          by_cases _hc : $condStx
          · simp only [_hc, if_true]  at _hpost ⊢; exact _hpost
          · simp only [_hc, if_false] at _hpost ⊢; exact _hpost))
      -- Discharge collected side conditions: chain disjointness +
      -- pcFree (from buildChainExpr) + branch-level disjointness (the
      -- three Disjoint metas just synthesized).
      let chainDisjs := (← disjGoals.get).reverse
      let branchDisjs := [disjBT, disjBF, disjTF].map (·.mvarId!)
      dischargeGoals (branchDisjs ++ chainDisjs)
        (← `(tactic| sl_disjoint_codereq)) "sl_disjoint_codereq"
      let pcfrees := (← pcfreeGoals.get).reverse
      dischargeGoals pcfrees (← `(tactic| sl_pcfree)) "sl_pcfree"

/-! ## sl_rw_abs — Gap-3 workaround helper

The `sl_block_iter` composition hits a kernel-level wall when SL atoms
contain `wrapAdd r10V (toU64 -80)`-shaped addresses (~96K `Nat.rec`
per iter at iter 5 of an 11-instruction macro — see
`[[sl-block-iter-perm-rewrite]]`). The cost is structural to the spec
form; surgical `@[irreducible]` attempts (Path A, 2026-05-17) confirmed
no kernel-attribute change moves the bottleneck without breaking other
proofs.

The proven workaround (in `pda_n1_stack_macro_spec`) is to parameterize
expensive atom addresses by abstract `Nat` variables with bridging
equalities, so the kernel's `isDefEq` sees clean atoms. This macro
reduces the manual rewrite boilerplate the workaround requires:

Before (manual):
```
rw [← hDesc] at h2
rw [← hDesc] at h4
rw [← hOut] at h9
```

After:
```
sl_rw_abs [hDesc, hOut] at [h2, h4, h9]
```

The macro applies `try rw [← hAbs] at hN` for each (abstraction,
hypothesis) cross-product, silently skipping cases where the rewrite
doesn't apply. Use it after constructing the per-step specs and
before `sl_block_iter`. -/

syntax "sl_rw_abs" "[" ident,* "]" "at" "[" ident,* "]" : tactic

open Lean Lean.Elab.Tactic in
elab_rules : tactic
  | `(tactic| sl_rw_abs [$abs,*] at [$hyps,*]) => withMainContext do
      for h in hyps.getElems do
        for a in abs.getElems do
          try
            evalTactic (← `(tactic| rw [← $a:ident] at $h:ident))
          catch _ => pure ()

/-! ## sl_reshape_pre / sl_reshape_post — permute a triple's pre/post

`sl_reshape_pre [a₀, …, aₖ]` reshapes the pre of a `cuTripleWithin(Mem)`
goal so the listed atoms come first and the rest become the trailing
frame, via `buildPermuteIff` + `cuTripleWithin{,Mem}_reshape_pre`. The
listed atoms must be a sub-multiset of the current pre (matched up to
`isDefEq` + address normalization). No-op if already in order. This is
the reusable permutation step for reshaping a lifted triple into a
refinement's `setupPre ** field-atoms …` shape. -/

open Lean Lean.Meta Lean.Elab.Tactic Lean.Elab.Term SLBlockIter in
/-- Shared core: `argIdx = 5` reshapes the pre, `6` the post. -/
private def slReshapeGoal (argIdx : Nat) (atoms : Array (TSyntax `term))
    (memLemma nonMemLemma : Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let isMem := ty.isAppOf ``SVM.SBPF.cuTripleWithinMem
  unless isMem || ty.isAppOf ``SVM.SBPF.cuTripleWithin do
    throwError "sl_reshape: goal is not a cuTripleWithin(Mem)"
  let args := ty.getAppArgs
  let cur := args[argIdx]!
  let src := flattenSepConj cur
  let tgt ← atoms.toList.mapM (fun s => elabTermAndSynthesize s.raw none)
  match ← buildPermuteIff src tgt with
  | none => throwError "sl_reshape: listed atoms are not a sub-multiset of the {if argIdx == 5 then "pre" else "post"}"
  | some (none, _, _) => pure ()           -- already in order
  | some (some iffFwd, frame, _) =>
    -- iffFwd : ∀ h, cur h ↔ new h ; reshape lemma wants `new ↔ cur`.
    let psType := Lean.mkConst ``SVM.SBPF.PartialState
    let iffRev ← withLocalDeclD `h psType fun h => do
      let applied ← mkAppM' iffFwd #[h]
      let symmed ← mkAppM ``Iff.symm #[applied]
      mkLambdaFVars #[h] symmed
    let newAtom ← rebuildSepConj (tgt ++ frame)
    let innerTy := mkAppN ty.getAppFn (args.set! argIdx newAtom)
    let innerMVar ← mkFreshExprMVar innerTy
    let lemmaName := if isMem then memLemma else nonMemLemma
    let proof ← mkAppM lemmaName #[iffRev, innerMVar]
    g.assign proof
    replaceMainGoal [innerMVar.mvarId!]

open Lean Lean.Elab.Tactic in
elab "sl_reshape_pre" "[" atoms:term,* "]" : tactic =>
  slReshapeGoal 5 atoms.getElems
    ``SVM.SBPF.cuTripleWithinMem_reshape_pre ``SVM.SBPF.cuTripleWithin_reshape_pre

open Lean Lean.Elab.Tactic in
elab "sl_reshape_post" "[" atoms:term,* "]" : tactic =>
  slReshapeGoal 6 atoms.getElems
    ``SVM.SBPF.cuTripleWithinMem_reshape_post ``SVM.SBPF.cuTripleWithin_reshape_post

/-! ## sl_exact — close a triple goal from a permutation-equal hypothesis

`sl_exact h` closes a `cuTripleWithin(Mem)` goal using `h : cuTripleWithin(Mem)`
with the same N/M/pc/cr/rr whose pre and post are the goal's pre/post up
to sep-conj permutation AND re-bracketing. This is what makes refinement
wiring ergonomic: after expanding the codec atoms, the goal's pre/post
are permutations of a framed lift triple's, and `sl_exact` matches them
(handling the non-right-folded `P ** F` bracketing `frame_right` produces). -/

open Lean Lean.Meta Lean.Elab.Tactic Lean.Elab.Term SLBlockIter in
/-- Pointwise iff `∀ s, A s ↔ B s` when `A`, `B` are the same atom
    multiset, composing `A ↔ rebuild(flatten A) ↔ rebuild(flatten B) ↔ B`
    (right-fold normalization on each side + the bubble-sort permutation). -/
private def buildMatchIff (A B : Expr) : MetaM Expr := do
  let fa := flattenSepConj A
  let fb := flattenSepConj B
  let permOpt ← match ← buildPermuteIff fa fb with
    | none => throwError m!"sl_exact: pre/post atoms are not a permutation"
    | some (permIff?, frame, _) =>
      unless frame.isEmpty do
        throwError m!"sl_exact: hypothesis has extra atoms not in the goal"
      pure permIff?   -- rebuild(fa) ↔ rebuild(faPermuted), or none if equal
  -- `faPermuted` = `fa`'s atoms reordered into `fb`'s order (the endpoint of
  -- `permOpt`). Its atoms are `A`'s representations, which may be defeq-but-not-
  -- syntactically-equal to `fb`'s (e.g. `effectiveAddr base 160` vs `base+160`).
  let faPermuted ← match ← bubbleSortToPrefix fa fb with
    | some (_, final) => pure (final.take fb.length)
    | none => throwError m!"sl_exact: pre/post atoms are not a permutation"
  let aRf ← buildRightFoldIff A   -- A ↔ rebuild(fa), or none
  let bRf ← buildRightFoldIff B   -- B ↔ rebuild(fb), or none
  -- rebuild(faPermuted) ↔ rebuild(fb): per-atom defeq bridge, `none` if equal.
  let bridge? ← buildDefeqBridge faPermuted fb
  -- Compose A ↔ rebuild(fa) ↔ rebuild(faPermuted) ↔ rebuild(fb) ↔ B (skipping
  -- the `none` refls; the final piece needs rebuild(fb) ↔ B = symm bRf).
  let pieces : List Expr := (aRf.toList) ++ permOpt.toList ++ bridge?.toList ++
    (← bRf.toList.mapM (fun e => mkAppM ``SVM.SBPF.sepConj_iff_symm_pw #[e]))
  match pieces with
  | [] => mkAppM ``SVM.SBPF.sepConj_iff_refl #[A]
  | p :: ps => ps.foldlM (fun acc e => mkAppM ``SVM.SBPF.sepConj_iff_trans_pw #[acc, e]) p

open Lean Lean.Meta Lean.Elab.Tactic Lean.Elab.Term SLBlockIter in
elab "sl_exact " ht:term : tactic => withMainContext do
  let h ← elabTermAndSynthesize ht none
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← g.getType)).consumeMData
  let hTy := (← instantiateMVars (← inferType h)).consumeMData
  let isMem := goalTy.isAppOf ``SVM.SBPF.cuTripleWithinMem
  unless isMem || goalTy.isAppOf ``SVM.SBPF.cuTripleWithin do
    throwError "sl_exact: goal is not a cuTripleWithin(Mem)"
  let gArgs := goalTy.getAppArgs
  let hArgs := hTy.getAppArgs
  let iffPre ← buildMatchIff hArgs[5]! gArgs[5]!   -- hPre ↔ goalPre
  let iffPost ← buildMatchIff hArgs[6]! gArgs[6]!  -- hPost ↔ goalPost
  -- reshape h's post then pre to the goal's, then it IS the goal.
  let h1 ← reshapeChainPost h isMem iffPost
  let h2 ← reshapeChainPre h1 isMem iffPre
  g.assign h2

end SVM.SBPF
