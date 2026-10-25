/-
  Guards as facts about the input. `PathCond` says a run took each guard's listed branch, a
  fact about the registers at that moment; `AbsInterp` says what those registers hold in
  terms of the run's initial input. `input_guards` combines them: for each guard whose
  compared operands are pinned by the abstract map (an input field or a constant), the
  guard's condition holds of the initial input bytes.
-/
import SVM.SBPF.PathCond
import SVM.SBPF.AbsInterp

namespace SVM.SBPF

open Memory

/-- A conditional jump's compared register, source operand, and target. -/
def Insn.jumpOps? : Insn → Option (Reg × Src × Nat)
  | .jeq d s t | .jne d s t | .jgt d s t | .jge d s t | .jlt d s t | .jle d s t
  | .jsgt d s t | .jsge d s t | .jslt d s t | .jsle d s t | .jset d s t
  | .jmp32 _ d s t => some (d, s, t)
  | _ => none

/-- When a conditional jump goes to its target, given its compared values. -/
def jumpCond : Insn → Nat → Nat → Prop
  | .jeq .., a, b => a = b
  | .jne .., a, b => a ≠ b
  | .jgt .., a, b => a > b
  | .jge .., a, b => a ≥ b
  | .jlt .., a, b => a < b
  | .jle .., a, b => a ≤ b
  | .jsgt .., a, b => toSigned64 a > toSigned64 b
  | .jsge .., a, b => toSigned64 a ≥ toSigned64 b
  | .jslt .., a, b => toSigned64 a < toSigned64 b
  | .jsle .., a, b => toSigned64 a ≤ toSigned64 b
  | .jset .., a, b => a &&& b ≠ 0
  | .jmp32 c .., a, b => jump32Holds c a b = true
  | _, _, _ => False

theorem step_pc_jump (insn : Insn) (d : Reg) (src : Src) (t : Nat)
    (h : insn.jumpOps? = some (d, src, t)) (s : State) :
    (step insn s).pc = t ∧ jumpCond insn (s.regs.get d) (resolveSrc s.regs src) ∨
      (step insn s).pc = s.pc + 1 ∧ ¬ jumpCond insn (s.regs.get d) (resolveSrc s.regs src) := by
  cases insn <;> simp only [Insn.jumpOps?, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> simp only [step, jumpCond] <;>
    split <;> simp_all

/-- The value an abstract value pins (`top` pins nothing; it is excluded by `iguardCheck`). -/
def AVal.val (s0 : State) : AVal → Nat
  | .top => 0
  | .const n => n
  | .inPtr off => INPUT_START + off
  | .fp => STACK_TOP
  | .inLoad w off => readByWidth s0.mem (INPUT_START + off) w

theorem AVal.denote_val {s0 : State} {x : AVal} {v : Nat} (hx : x ≠ .top)
    (h : x.denote s0 v) : v = x.val s0 := by
  cases x <;> first | exact absurd rfl hx | exact h

/-- A guard whose compared operands the abstract map pins. -/
structure IGuard where
  g : Guard
  dv : AVal
  sv : AVal
  deriving Repr

/-- The guard's condition, as a fact about the initial input. -/
def IGuard.holds (s0 : State) (ig : IGuard) : Prop :=
  match ig.g.insn.jumpOps? with
  | some (_, _, t) => (jumpCond ig.g.insn (ig.dv.val s0) (ig.sv.val s0) ↔ ig.g.onSucc = t)
  | none => True

/-- The map pins the guard's operands to `dv`/`sv`, and its two branches differ. -/
def iguardCheck (m : Array (Option AState)) (ig : IGuard) : Bool :=
  match ig.g.insn.jumpOps?, m.getD ig.g.pc none with
  | some (d, src, t), some a =>
    t != ig.g.pc + 1 && ig.dv != .top && ig.sv != .top && a.get d == ig.dv &&
      (match src with
       | .imm i => ig.sv == .const (toU64 i)
       | .reg r => a.get r == ig.sv)
  | _, _ => false

theorem PassedGuards.shift {fetch : Nat → Option Insn} {s : State} {j k : Nat}
    {gs : List Guard} (h : PassedGuards fetch (executeFn fetch s j) k gs) :
    PassedGuards fetch s (j + k) gs := by
  intro g hg
  obtain ⟨i, hi, h1, h2, h3, h4⟩ := h g hg
  rw [← executeFn_compose] at h1 h2 h3 h4
  exact ⟨j + i, by omega, h1, h2, h3, h4⟩

theorem PassedGuards.sub {fetch : Nat → Option Insn} {s : State} {n : Nat}
    {gs gs' : List Guard} (h : PassedGuards fetch s n gs) (hsub : ∀ g ∈ gs', g ∈ gs) :
    PassedGuards fetch s n gs' :=
  fun g hg => h g (hsub g hg)

/-- **Guards about the input.** If a run from `s0` passed the guards of `igs` and the
    abstract map (checked by `absCheck`) pins their operands, each guard's condition holds of
    `s0`'s input. -/
theorem input_guards (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (m : Array (Option AState)) (entry : Nat)
    (init : AState) (habs : absCheck fetch noret m entry init = true) (s0 : State)
    (hpc : s0.pc = entry) (hcs : s0.callStack = []) (hinit : Concrete s0 init s0) (n : Nat)
    (igs : List IGuard) (hpass : PassedGuards fetch s0 n (igs.map (·.g)))
    (hig : igs.all (iguardCheck m) = true) :
    ∀ ig ∈ igs, ig.holds s0 := by
  intro ig hmem
  obtain ⟨j, _, hcsj, hpcj, _, hstep⟩ := hpass ig.g (List.mem_map_of_mem hmem)
  obtain ⟨a, ha, hc⟩ := abs_sound fetch noret hNR m entry init habs s0 hpc hcs hinit j hcsj
  have hchk := List.all_eq_true.mp hig ig hmem
  unfold iguardCheck at hchk
  unfold IGuard.holds
  rw [hpcj] at ha
  revert hchk
  cases hops : ig.g.insn.jumpOps? with
  | none => intro h; cases h
  | some ops =>
  obtain ⟨d, src, t⟩ := ops
  rw [ha]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  intro ⟨⟨⟨⟨ht, hdv⟩, hsv⟩, hd⟩, hsrc⟩
  have hdval : (executeFn fetch s0 j).regs.get d = ig.dv.val s0 :=
    AVal.denote_val hdv (hd ▸ hc.1 d)
  have hsval : resolveSrc (executeFn fetch s0 j).regs src = ig.sv.val s0 := by
    cases src with
    | imm i =>
      simp only at hsrc
      rw [beq_iff_eq.mp hsrc]; rfl
    | reg r =>
      simp only at hsrc
      exact AVal.denote_val hsv (by rw [← beq_iff_eq.mp hsrc]; exact hc.1 r)
  rcases step_pc_jump ig.g.insn d src t hops (executeFn fetch s0 j) with
    ⟨hp, hcond⟩ | ⟨hp, hcond⟩ <;> rw [hdval, hsval] at hcond <;> rw [hstep] at hp
  · exact ⟨fun _ => hp, fun _ => hcond⟩
  · rw [hpcj] at hp
    exact ⟨fun h => absurd h hcond, fun h => absurd (h.symm.trans hp) ht⟩

/-- An edge's routes, with the input-pinned subset of each route's guards. -/
abbrev IRoute := Nat × List IGuard × List IGuard

/-- Every `IGuard` list is drawn from its guard list, route by route. -/
def iguardsMatch (dom : List Guard) (routes : List Route) (idom : List IGuard)
    (iroutes : List IRoute) : Bool :=
  (idom.map (·.g)).all (dom.contains ·) &&
    routes.all fun (c, pre, post) => iroutes.any fun (c', ip, iq) =>
      c' == c && (ip.map (·.g)).all (pre.contains ·) && (iq.map (·.g)).all (post.contains ·)

theorem sub_of_all_contains {gs : List Guard} {igs : List IGuard}
    (h : (igs.map (·.g)).all (gs.contains ·) = true) : ∀ g ∈ igs.map (·.g), g ∈ gs := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simpa using this

/-- **Input conditions of an edge.** If the path and abstract-map checks pass, every
    top-level run from `s0` (at `entry`, described by `init`) that stands at `e` started from
    an input satisfying the edge's pinned dominating guards and one route's pinned guards. -/
theorem edge_input_conditions (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (size entry e : Nat)
    (dom : List Guard) (routes : List Route) (idom : List IGuard) (iroutes : List IRoute)
    (m : Array (Option AState)) (init : AState)
    (hpath : edgeCheck fetch noret size entry e dom routes = true)
    (habs : absCheck fetch noret m entry init = true)
    (hpin : (idom.all (iguardCheck m) &&
      iroutes.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) = true)
    (hmatch : iguardsMatch dom routes idom iroutes = true)
    (s0 : State) (hpc : s0.pc = entry) (hcs : s0.callStack = []) (hinit : Concrete s0 init s0)
    (n : Nat) (hend : (executeFn fetch s0 n).callStack = [] ∧ (executeFn fetch s0 n).pc = e) :
    (∀ ig ∈ idom, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  simp only [Bool.and_eq_true] at hpin
  obtain ⟨hpdom, hproutes⟩ := hpin
  simp only [iguardsMatch, Bool.and_eq_true] at hmatch
  obtain ⟨hmdom, hmroutes⟩ := hmatch
  obtain ⟨hdom, c, pre, post, hr, j, hj, hcsj, h0j, hpcj, hpre, hpost⟩ :=
    edge_path_condition fetch noret hNR size entry e dom routes hpath s0 hpc hcs n hend
  have ig := input_guards fetch noret hNR m entry init habs s0 hpc hcs hinit
  refine ⟨ig n idom (hdom.sub (sub_of_all_contains hmdom)) hpdom, ?_⟩
  have hany := List.any_eq_true.mp (List.all_eq_true.mp hmroutes _ hr)
  obtain ⟨⟨c', ip, iq⟩, hir, hm⟩ := hany
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨_, hip⟩, hiq⟩ := hm
  have hpi := List.all_eq_true.mp hproutes _ hir
  simp only [Bool.and_eq_true] at hpi
  refine ⟨c', ip, iq, hir, ig j ip (hpre.sub (sub_of_all_contains hip)) hpi.1, ?_⟩
  have hq : PassedGuards fetch s0 (j + (n - j)) (iq.map (·.g)) :=
    PassedGuards.shift (hpost.sub (sub_of_all_contains hiq))
  exact ig (j + (n - j)) iq hq hpi.2

end SVM.SBPF
