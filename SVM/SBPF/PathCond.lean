/-
  Path conditions from static reachability. For a target PC `e` and a list of guards
  (conditional jumps with one successor that can reach `e` and one that cannot), every
  top-level run from the entry that stands at `e` visited each guard that dominates `e` and
  took its `e`-ward branch there (`path_condition`). Everything program-specific is a Bool
  check (`guardsCheck`) meant for `native_decide` over the decoded program: the reachable
  sets are computed by BFS here, and only their closure is trusted, so the BFS itself needs
  no proof.
-/
import SVM.SBPF.StaticReach

namespace SVM.SBPF

/-! ## Computing reachable sets -/

/-- Static successors of whatever `fetch` serves at `pc`. -/
def succOf (fetch : Nat → Option Insn) (noret : Nat → Bool) (pc : Nat) : List Nat :=
  match fetch pc with
  | some insn => callSucc noret pc insn
  | none => []

/-- Worklist BFS over `next`, bounded by `fuel` pops; returns the visited bitmap. -/
def bfs (next : Nat → List Nat) (size : Nat) (starts : List Nat) (stop : Nat → Bool)
    (fuel : Nat) : Array Bool :=
  go (starts.foldl (fun a p => a.setIfInBounds p true) (Array.replicate size false)) starts fuel
where
  go (seen : Array Bool) (work : List Nat) : Nat → Array Bool
    | 0 => seen
    | fuel + 1 =>
      match work with
      | [] => seen
      | p :: rest =>
        if stop p then go seen rest fuel
        else
          let new := (next p).filter fun q => q < size && !(seen.getD q false)
          go (new.foldl (fun a q => a.setIfInBounds q true) seen) (new ++ rest) fuel

/-- PCs reachable from `start` without expanding `stop`. -/
def reachAvoid (fetch : Nat → Option Insn) (noret : Nat → Bool) (size start : Nat)
    (stop : Nat → Bool) : Array Bool :=
  bfs (succOf fetch noret) size [start] stop (size + 1)

/-- PCs that can statically reach `e` (backward BFS). -/
def canReach (fetch : Nat → Option Insn) (noret : Nat → Bool) (size e : Nat) : Array Bool :=
  let preds : Array (List Nat) := (List.range size).foldl (fun a p =>
      (succOf fetch noret p).foldl (fun a q => if q < size then a.modify q (p :: ·) else a) a)
    (Array.replicate size [])
  bfs (fun q => preds.getD q []) size [e] (fun _ => false) (size + 1)

/-! ## Checking closure -/

/-- Bool form of `ClosedExcept` for a bitmap, checked below `size` (the bitmap is `false`
    beyond its size). -/
def closedCheck (fetch : Nat → Option Insn) (noret : Nat → Bool) (R : Array Bool)
    (G : Nat → Bool) : Bool :=
  (List.range R.size).all fun pc =>
    !(R.getD pc false) || G pc ||
      match fetch pc with
      | none => true
      | some (.callx _) => false
      | some insn => (callSucc noret pc insn).all fun q => R.getD q false

theorem closedExcept_of_check (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (R : Array Bool) (G : Nat → Bool) (h : closedCheck fetch noret R G = true) :
    ClosedExcept fetch noret (fun pc => R.getD pc false) G := by
  intro pc hR hG insn hf
  have hlt : pc < R.size := by
    cases Nat.lt_or_ge pc R.size with
    | inl h => exact h
    | inr hge =>
      have : R.getD pc false = false := by simp [Array.getD, Nat.not_lt.mpr hge]
      simp [this] at hR
  have := List.all_eq_true.mp h pc (List.mem_range.mpr hlt)
  simp only [hR, hG, hf, Bool.not_true, Bool.false_or] at this
  cases insn
  case callx reg => cases this
  all_goals
    refine ⟨(fun reg h => by cases h), fun q hq => ?_⟩
    exact List.all_eq_true.mp this q hq

/-! ## Guards -/

/-- A conditional jump at `pc` that must take its branch to `onSucc` on the way to the target. -/
structure Guard where
  pc : Nat
  insn : Insn
  onSucc : Nat
  deriving Repr, DecidableEq

/-- A conditional jump goes to its target or falls through. -/
def Insn.jumpTarget? : Insn → Option Nat
  | .jeq _ _ t | .jne _ _ t | .jgt _ _ t | .jge _ _ t | .jlt _ _ t | .jle _ _ t
  | .jsgt _ _ t | .jsge _ _ t | .jslt _ _ t | .jsle _ _ t | .jset _ _ t
  | .jmp32 _ _ _ t => some t
  | _ => none

theorem step_jump_pc (insn : Insn) (t : Nat) (h : insn.jumpTarget? = some t) (s : State) :
    (step insn s).pc = t ∨ (step insn s).pc = s.pc + 1 := by
  cases insn <;> simp [Insn.jumpTarget?] at h <;> subst h <;> simp only [step] <;> split <;>
    simp

/-- The branch away from `onSucc`. -/
def Guard.offSucc (g : Guard) : Nat :=
  match g.insn.jumpTarget? with
  | some t => if t = g.onSucc then g.pc + 1 else t
  | none => g.pc

/-- Everything `path_condition` needs of one guard, against target `e`, entry `entry`,
    the `e`-avoiding set `notE` (complement of `canReach e`), and a program of `size` PCs. -/
def guardCheck (fetch : Nat → Option Insn) (noret : Nat → Bool) (size entry e : Nat)
    (notE : Array Bool) (g : Guard) : Bool :=
  let R := reachAvoid fetch noret size entry (· == g.pc)
  decide (fetch g.pc = some g.insn) && g.insn.jumpTarget?.isSome &&
    (g.insn.jumpTarget? == some g.onSucc || g.onSucc == g.pc + 1) &&
    notE.getD g.offSucc false && !(notE.getD g.onSucc false) && g.pc != e &&
    R.getD entry false && !(R.getD e false) && closedCheck fetch noret R (· == g.pc)

/-- All guards of a target, plus closure of its `e`-avoiding set: the PCs reachable from the
    entry that cannot reach `e` (restricted to the entry's reach so unrelated code, e.g. a
    `callx` elsewhere, does not matter). -/
def guardsCheck (fetch : Nat → Option Insn) (noret : Nat → Bool) (size entry e : Nat)
    (gs : List Guard) : Bool :=
  let reach := reachAvoid fetch noret size entry (fun _ => false)
  let notE := Array.zipWith (fun r c => r && !c) reach (canReach fetch noret size e)
  !(notE.getD e false) && closedCheck fetch noret notE (fun _ => false) &&
    gs.all (guardCheck fetch noret size entry e notE)

/-- The run from `s` passed every guard of `gs` within `n` steps, at top level and running,
    taking the guard's listed branch. -/
def PassedGuards (fetch : Nat → Option Insn) (s : State) (n : Nat) (gs : List Guard) : Prop :=
  ∀ g ∈ gs, ∃ j, j ≤ n ∧ (executeFn fetch s j).callStack = [] ∧
    (executeFn fetch s j).pc = g.pc ∧ (executeFn fetch s j).exitCode = none ∧
    (step g.insn (executeFn fetch s j)).pc = g.onSucc

/-- **Path condition.** If the check passes, every top-level run from `entry` that stands at
    `e` at top level visited each guard, running and at top level, and the guard's step went
    to its `e`-ward successor. -/
theorem path_condition (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (size entry e : Nat) (gs : List Guard)
    (hchk : guardsCheck fetch noret size entry e gs = true) (s : State) (hpc : s.pc = entry)
    (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn fetch s n).callStack = [] ∧ (executeFn fetch s n).pc = e) :
    PassedGuards fetch s n gs := by
  intro g hg
  simp only [guardsCheck, Bool.and_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨heN, hNc⟩, hall⟩ := hchk
  have hgc := List.all_eq_true.mp hall g hg
  simp only [guardCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at hgc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hf, hjt⟩, hon⟩, hoff⟩, hon'⟩, hne⟩, hRe⟩, hRe'⟩, hRc⟩ := hgc
  -- the run visited the guard
  obtain ⟨j, hj, hcsj, hGj, h0j, hcont⟩ :=
    visits_before fetch noret hNR _ (· == g.pc) (closedExcept_of_check fetch noret _ _ hRc) s
      (by rw [hpc]; exact hRe) hcs e n hRe' hend
  have hpcj : (executeFn fetch s j).pc = g.pc := by simpa using hGj
  refine ⟨j, hj, hcsj, hpcj, h0j, ?_⟩
  -- and its step did not leave toward the `e`-avoiding side
  have hnc : ∀ t, g.insn ≠ .call_local t := by
    intro t ht; rw [ht] at hjt; simp [Insn.jumpTarget?] at hjt
  have hnx : ∀ reg, g.insn ≠ .callx reg := by
    intro r hr; rw [hr] at hjt; simp [Insn.jumpTarget?] at hjt
  have hstep := guard_toward fetch noret hNR _ (closedExcept_of_check fetch noret _ _ hNc) e heN
    (executeFn fetch s j) hcsj h0j g.insn (by rw [hpcj]; exact hf) hnc hnx
    (by rw [hpcj]; exact hne) (n - j) (by rw [← hcont]; exact hend)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hjt
  have hoffdef : g.offSucc = if t = g.onSucc then g.pc + 1 else t := by
    simp [Guard.offSucc, ht]
  rcases step_jump_pc g.insn t ht (executeFn fetch s j) with h | h
  · rw [h] at hstep ⊢
    by_cases htt : t = g.onSucc
    · exact htt
    · rw [hoffdef, if_neg htt] at hoff; rw [hoff] at hstep; cases hstep
  · rw [hpcj] at h; rw [h] at hstep ⊢
    by_cases h1 : g.pc + 1 = g.onSucc
    · exact h1
    · exfalso
      simp only [Bool.or_eq_true, beq_iff_eq, ht] at hon
      rcases hon with hon | hon
      · have htt : t = g.onSucc := Option.some.inj hon
        rw [hoffdef, if_pos htt] at hoff; rw [hoff] at hstep; cases hstep
      · exact h1 hon.symm

/-- Every route from `entry` to `e` passes one of `stops` (Bool check). -/
def visitsCheck (fetch : Nat → Option Insn) (noret : Nat → Bool) (size entry e : Nat)
    (stops : List Nat) : Bool :=
  let R := reachAvoid fetch noret size entry (stops.contains ·)
  R.getD entry false && !(R.getD e false) && closedCheck fetch noret R (stops.contains ·)

/-- **Cut.** If the check passes, every top-level run from `entry` that stands at `e` at top
    level visited one of `stops` first, running and at top level. -/
theorem visits_one_of (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (size entry e : Nat) (stops : List Nat)
    (hchk : visitsCheck fetch noret size entry e stops = true) (s : State) (hpc : s.pc = entry)
    (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn fetch s n).callStack = [] ∧ (executeFn fetch s n).pc = e) :
    ∃ j, j ≤ n ∧ (executeFn fetch s j).callStack = [] ∧
      (executeFn fetch s j).pc ∈ stops ∧ (executeFn fetch s j).exitCode = none ∧
      executeFn fetch s n = executeFn fetch (executeFn fetch s j) (n - j) := by
  simp only [visitsCheck, Bool.and_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨hRs, hRe⟩, hRc⟩ := hchk
  obtain ⟨j, hj, h1, h2, h3, h4⟩ :=
    visits_before fetch noret hNR _ _ (closedExcept_of_check fetch noret _ _ hRc) s
      (by rw [hpc]; exact hRs)
      hcs e n hRe hend
  exact ⟨j, hj, h1, by simpa using h2, h3, h4⟩

/-! ## Success edges -/

/-- An authority-style route to an edge: a checkpoint every route must pass, with its guards
    from the entry and its guards on to the edge. -/
abbrev Route := Nat × List Guard × List Guard

/-- Everything `edge_path_condition` needs: the edge's own dominating guards, that the
    routes' checkpoints cut every path to it, and each route's guards. -/
def edgeCheck (fetch : Nat → Option Insn) (noret : Nat → Bool) (size entry e : Nat)
    (dom : List Guard) (routes : List Route) : Bool :=
  guardsCheck fetch noret size entry e dom &&
    visitsCheck fetch noret size entry e (routes.map (·.1)) &&
    routes.all fun (c, pre, post) =>
      guardsCheck fetch noret size entry c pre && guardsCheck fetch noret size c e post

/-- **Edge path condition.** If the check passes, every top-level run from `entry` that stands
    at `e` passed `e`'s dominating guards and passed through one route's checkpoint `c` after
    `j` steps, having passed that route's guards before and after it. -/
theorem edge_path_condition (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (size entry e : Nat) (dom : List Guard)
    (routes : List Route) (hchk : edgeCheck fetch noret size entry e dom routes = true)
    (s : State) (hpc : s.pc = entry) (hcs : s.callStack = []) (n : Nat)
    (hend : (executeFn fetch s n).callStack = [] ∧ (executeFn fetch s n).pc = e) :
    PassedGuards fetch s n dom ∧
    ∃ c pre post, (c, pre, post) ∈ routes ∧ ∃ j, j ≤ n ∧
      (executeFn fetch s j).callStack = [] ∧ (executeFn fetch s j).exitCode = none ∧
      (executeFn fetch s j).pc = c ∧ PassedGuards fetch s j pre ∧
      PassedGuards fetch (executeFn fetch s j) (n - j) post := by
  simp only [edgeCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨hdom, hvis⟩, hroutes⟩ := hchk
  refine ⟨path_condition fetch noret hNR size entry e dom hdom s hpc hcs n hend, ?_⟩
  obtain ⟨j, hj, hcsj, hmem, h0j, hcont⟩ :=
    visits_one_of fetch noret hNR size entry e _ hvis s hpc hcs n hend
  have hrest : (executeFn fetch (executeFn fetch s j) (n - j)).callStack = [] ∧
      (executeFn fetch (executeFn fetch s j) (n - j)).pc = e := by rw [← hcont]; exact hend
  obtain ⟨⟨c, pre, post⟩, hr, hc⟩ := List.mem_map.mp hmem
  have hrc := List.all_eq_true.mp hroutes _ hr
  simp only [Bool.and_eq_true] at hrc
  refine ⟨c, pre, post, hr, j, hj, hcsj, h0j, hc.symm, ?_, ?_⟩
  · exact path_condition fetch noret hNR size entry c pre hrc.1 s hpc hcs j ⟨hcsj, hc.symm⟩
  · exact path_condition fetch noret hNR size c e post hrc.2 _ hc.symm hcsj (n - j) hrest

end SVM.SBPF
