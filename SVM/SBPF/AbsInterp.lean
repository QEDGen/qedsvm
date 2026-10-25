/-
  A checked abstract interpretation of top-level runs. Each PC gets an abstract state saying,
  per register, what is known about its value in terms of the run's initial state `s0`: a
  constant, a pointer into the input buffer, the frame pointer, or a value loaded from a fixed
  input offset; plus whether the input buffer is still unwritten. A Lean worklist computes the
  map (unverified); `absCheck` checks that it is a post-fixpoint of the transfer function over
  the static CFG (`callSucc`), and `abs_sound` turns a passing check into: every top-level
  state of the run satisfies its PC's abstract state.

  Internal calls keep r6-r10 (`callee_returns_or_faults` restores them) and forget r0-r5 and
  the input; syscalls forget everything but r10 and the input. Stores through the frame
  pointer cannot reach the input buffer, so they keep it. This is what turns a guard fact
  about registers (`PathCond`) into a fact about the input accounts.
-/
import SVM.SBPF.StaticReach

namespace SVM.SBPF

open Memory

/-! ## Invariants of top-level runs -/

/-- **Invariant rule.** A property of top-level states holds of every top-level state of a
    run if it holds at the start, survives every top-level step that is not a call, survives
    a fault in place, and holds at every state a call could return to (same r6-r10, at the
    return PC; everything else arbitrary). Calls into `noret` targets never return. -/
theorem inv_holds (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (Inv : State → Prop)
    (hbad : ∀ s e v, Inv s → Inv { s with exitCode := e, vmError := v })
    (hstep : ∀ s insn, s.callStack = [] → s.exitCode = none → Inv s →
      fetch s.pc = some insn → (∀ t, insn ≠ .call_local t) → (∀ r, insn ≠ .callx r) →
      Inv (chargeCu (step insn s)))
    (hnox : ∀ s r, s.callStack = [] → Inv s → fetch s.pc ≠ some (.callx r))
    (hcall : ∀ s t, s.callStack = [] → s.exitCode = none → Inv s →
      fetch s.pc = some (.call_local t) → noret t = false →
      ∀ u : State, u.callStack = [] → u.pc = s.pc + 1 → u.regs.r6 = s.regs.r6 →
        u.regs.r7 = s.regs.r7 → u.regs.r8 = s.regs.r8 → u.regs.r9 = s.regs.r9 →
        u.regs.r10 = s.regs.r10 → u.exitCode = none → Inv u) :
    ∀ (n : Nat) (s : State), s.callStack = [] → Inv s →
      (executeFn fetch s n).callStack = [] → Inv (executeFn fetch s n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s hcs hI hend
  cases n with
  | zero => simpa using hI
  | succ n =>
  cases h0 : s.exitCode with
  | some c => rw [executeFn_halted fetch s _ c h0]; exact hI
  | none =>
  by_cases hover : s.cuConsumed > s.cuBudget
  · rw [executeFn_overBudget fetch s _ h0 hover]; exact hI
  have hle : s.cuConsumed ≤ s.cuBudget := Nat.le_of_not_lt hover
  cases hf : fetch s.pc with
  | none =>
    have hbad' : executeFn fetch s (n + 1)
        = { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc } := by
      simp [executeFn, h0, hf, Nat.not_lt.mpr hle]
    rw [hbad']; exact hbad s _ _ hI
  | some insn =>
  rw [executeFn_step fetch s n insn h0 hle hf] at hend ⊢
  have hnx : ∀ r, insn ≠ .callx r := fun r h => hnox s r hcs hI (h ▸ hf)
  by_cases hcl : ∃ t, insn = .call_local t
  · obtain ⟨t, rfl⟩ := hcl
    have hdepth : ¬ s.callStack.length ≥ MAX_CALL_DEPTH := by
      rw [hcs]; simp [MAX_CALL_DEPTH]
    let F0 : CallFrame :=
      { retPc := s.pc + 1, savedR6 := s.regs.r6, savedR7 := s.regs.r7,
        savedR8 := s.regs.r8, savedR9 := s.regs.r9, savedR10 := s.regs.r10 }
    let v := chargeCu (step (.call_local t) s)
    have hv0 : v.exitCode = none := by simp [v, step, hdepth, h0]
    have hvcs : v.callStack = [] ++ F0 :: [] := by
      show (step (.call_local t) s).callStack = _
      simp only [step, if_neg hdepth]; rw [hcs]; rfl
    cases hnr : noret t with
    | true =>
      obtain ⟨ys, hys⟩ := hNR t hnr v F0 [] (by simp [v, step, hdepth]) hvcs hv0 n
      rw [hys] at hend; simp at hend
    | false =>
    rcases callee_returns_or_faults fetch F0 [] n v [] hv0 hvcs with
      ⟨ys', hcs', _⟩ | ⟨j, u, _, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, -, hu9⟩
    · rw [hcs'] at hend; simp at hend
    · have hIu := hcall s t hcs h0 hI hf hnr u hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8
      show Inv (executeFn fetch v n)
      rw [hu9] at hend ⊢
      exact ih (n - j) (by omega) u hu1 hIu hend
  · have hnc : ∀ t, insn ≠ .call_local t := fun t h => hcl ⟨t, h⟩
    have hcs' : (chargeCu (step insn s)).callStack = [] :=
      (step_static insn s hcs hnc hnx).1
    exact ih n (by omega) _ hcs' (hstep s insn hcs h0 hI hf hnc hnx) hend

/-! ## The abstract domain -/

/-- The frame pointer at top level. -/
def STACK_TOP : Nat := STACK_START + 0x1000

/-- What is known about one register, relative to the run's initial state. -/
inductive AVal where
  | top
  | const (n : Nat)
  /-- `INPUT_START + off`. -/
  | inPtr (off : Nat)
  /-- The top-level frame pointer. -/
  | fp
  /-- The value loaded from the initial input at `INPUT_START + off`. -/
  | inLoad (w : Width) (off : Nat)
  deriving DecidableEq, Repr

def AVal.denote (s0 : State) : AVal → Nat → Prop
  | .top, _ => True
  | .const n, v => v = n
  | .inPtr off, v => v = INPUT_START + off
  | .fp, v => v = STACK_TOP
  | .inLoad w off, v => v = readByWidth s0.mem (INPUT_START + off) w

/-- One abstract state: a value per register and whether the input is still unwritten. -/
structure AState where
  r0 : AVal := .top
  r1 : AVal := .top
  r2 : AVal := .top
  r3 : AVal := .top
  r4 : AVal := .top
  r5 : AVal := .top
  r6 : AVal := .top
  r7 : AVal := .top
  r8 : AVal := .top
  r9 : AVal := .top
  r10 : AVal := .top
  memSame : Bool := false
  deriving DecidableEq, Repr

def AState.get (a : AState) : Reg → AVal
  | .r0 => a.r0 | .r1 => a.r1 | .r2 => a.r2 | .r3 => a.r3 | .r4 => a.r4 | .r5 => a.r5
  | .r6 => a.r6 | .r7 => a.r7 | .r8 => a.r8 | .r9 => a.r9 | .r10 => a.r10

/-- Like `RegFile.set`, writing `r10` is a no-op. -/
def AState.set (a : AState) : Reg → AVal → AState
  | .r0, v => { a with r0 := v } | .r1, v => { a with r1 := v } | .r2, v => { a with r2 := v }
  | .r3, v => { a with r3 := v } | .r4, v => { a with r4 := v } | .r5, v => { a with r5 := v }
  | .r6, v => { a with r6 := v } | .r7, v => { a with r7 := v } | .r8, v => { a with r8 := v }
  | .r9, v => { a with r9 := v } | .r10, _ => a

/-- The input buffer still holds the initial bytes. -/
def MemSame (s0 s : State) : Prop := ∀ x, INPUT_START ≤ x → s.mem.read x = s0.mem.read x

def Concrete (s0 : State) (a : AState) (s : State) : Prop :=
  (∀ r, (a.get r).denote s0 (s.regs.get r)) ∧ (a.memSame = true → MemSame s0 s)

/-! ## Transfer function -/

/-- After a syscall: only r10 and nothing about the input survive. -/
def AState.afterSyscall (a : AState) : AState := { r10 := a.r10 }

/-- After an internal call returns: r6-r10 survive. -/
def AState.afterCall (a : AState) : AState :=
  { r6 := a.r6, r7 := a.r7, r8 := a.r8, r9 := a.r9, r10 := a.r10 }

/-- A store keeps the input only when it goes through the frame pointer with a small offset. -/
def AState.afterStore (a : AState) (dst : Reg) (off : Int) : AState :=
  if a.get dst = .fp ∧ off ≤ 0x1000 then a else { a with memSame := false }

def absStep (a : AState) : Insn → AState
  | .lddw dst imm => a.set dst (.const (toU64 imm))
  | .mov64 dst (.imm i) => a.set dst (.const (toU64 i))
  | .mov64 dst (.reg r) => a.set dst (a.get r)
  | .ldx w dst src off =>
    a.set dst (match a.get src, a.memSame with
      | .inPtr o, true => if 0 ≤ (o : Int) + off then .inLoad w ((o : Int) + off).toNat else .top
      | _, _ => .top)
  | .st _ dst off _ => a.afterStore dst off
  | .stx _ dst off _ => a.afterStore dst off
  | .add64 d _ | .sub64 d _ | .mul64 d _ | .div64 d _ | .mod64 d _ | .or64 d _ | .and64 d _
  | .xor64 d _ | .lsh64 d _ | .rsh64 d _ | .arsh64 d _ | .neg64 d
  | .add32 d _ | .sub32 d _ | .mul32 d _ | .div32 d _ | .mod32 d _ | .or32 d _ | .and32 d _
  | .xor32 d _ | .lsh32 d _ | .rsh32 d _ | .arsh32 d _ | .mov32 d _ | .neg32 d
  | .endian d _ _ => a.set d .top
  | .call _ => a.afterSyscall
  | .call_local _ => a.afterCall
  | _ => a

/-! ## Soundness of one step -/

theorem concrete_regs_mem {s0 : State} {a : AState} {s t : State} (hc : Concrete s0 a s)
    (hr : t.regs = s.regs) (hm : t.mem = s.mem) : Concrete s0 a t :=
  ⟨fun r => by rw [hr]; exact hc.1 r, fun h x hx => by rw [hm]; exact hc.2 h x hx⟩

theorem AState.get_set_same (a : AState) (d : Reg) (X : AVal) (hd : d ≠ .r10) :
    (a.set d X).get d = X := by
  cases d <;> first | rfl | exact absurd rfl hd

theorem AState.get_set_other (a : AState) (d r : Reg) (X : AVal) (h : r ≠ d) :
    (a.set d X).get r = a.get r := by
  cases d <;> cases r <;> first | rfl | exact absurd rfl h

theorem AState.set_memSame (a : AState) (d : Reg) (X : AVal) :
    (a.set d X).memSame = a.memSame := by cases d <;> rfl

/-- Writing a register: the written value must match `X` (unless it is `r10`, which neither
    side changes); everything else carries over. -/
theorem concrete_set {s0 : State} {a : AState} {s t : State} (hc : Concrete s0 a s)
    (d : Reg) (v : Nat) (X : AVal) (hX : d ≠ .r10 → X.denote s0 v)
    (hr : t.regs = s.regs.set d v) (hm : t.mem = s.mem) : Concrete s0 (a.set d X) t := by
  refine ⟨fun r => ?_, fun h x hx => by
    rw [AState.set_memSame] at h; rw [hm]; exact hc.2 h x hx⟩
  rw [hr]
  by_cases hd : d = .r10
  · subst hd
    have : a.set .r10 X = a := rfl
    rw [this, RegFile.set_r10]
    exact hc.1 r
  by_cases hrd : r = d
  · subst hrd
    rw [AState.get_set_same a r X hd, RegFile.get_set_self _ _ _ hd]
    exact hX hd
  · rw [AState.get_set_other a d r X hrd, RegFile.get_set_diff _ _ _ _ hrd]
    exact hc.1 r

theorem writeByWidth_read_far (m : Memory.Mem) (addr val : Nat) (w : Width) (x : Nat)
    (hx : addr + 8 ≤ x) : (writeByWidth m addr val w).read x = m.read x := by
  cases w
  · exact writeU8_read_other m addr val x (by omega)
  · exact writeU16_read_other m addr val x (by omega) (by omega)
  · exact writeU32_read_other m addr val x (by omega) (by omega) (by omega) (by omega)
  · exact writeU64_read_other m addr val x (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)

theorem readByWidth_congr (m1 m2 : Memory.Mem) (addr : Nat) (w : Width)
    (h : ∀ i, i < 8 → m1.read (addr + i) = m2.read (addr + i)) :
    readByWidth m1 addr w = readByWidth m2 addr w := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega); have h4 := h 4 (by omega); have h5 := h 5 (by omega)
  have h6 := h 6 (by omega); have h7 := h 7 (by omega)
  simp only [Nat.add_zero] at h0
  cases w <;> simp only [readByWidth, readU8, readU16, readU32, readU64, h0, h1, h2, h3, h4,
    h5, h6, h7]

theorem effectiveAddr_input (o : Nat) (off : Int) (h : 0 ≤ (o : Int) + off) :
    effectiveAddr (INPUT_START + o) off = INPUT_START + ((o : Int) + off).toNat := by
  unfold effectiveAddr; omega

theorem ldx_value_sound (s0 s : State) (a : AState) (hc : Concrete s0 a s) (w : Width)
    (src : Reg) (off : Int) :
    (match a.get src, a.memSame with
      | .inPtr o, true => if 0 ≤ (o : Int) + off then AVal.inLoad w ((o : Int) + off).toNat
          else .top
      | _, _ => .top).denote s0 (readByWidth s.mem (effectiveAddr (s.regs.get src) off) w) := by
  have hsrc := hc.1 src
  cases hg : a.get src <;> cases hm : a.memSame
  all_goals first | exact trivial | skip
  rename_i o
  rw [hg] at hsrc
  simp only [AVal.denote] at hsrc
  show (if 0 ≤ (o : Int) + off then AVal.inLoad w ((o : Int) + off).toNat else AVal.top).denote
    s0 _
  split
  · rename_i hpos
    show _ = _
    rw [hsrc, effectiveAddr_input o off hpos]
    apply readByWidth_congr
    intro i _
    exact hc.2 hm _ (by omega)
  · trivial

theorem store_keeps (s0 s : State) (a : AState) (hc : Concrete s0 a s) (dst : Reg) (off : Int)
    (val : Nat) (w : Width) :
    Concrete s0 (a.afterStore dst off)
      { s with mem := writeByWidth s.mem (effectiveAddr (s.regs.get dst) off) val w,
               pc := s.pc + 1 } := by
  unfold AState.afterStore
  split
  · rename_i h
    obtain ⟨hfp, hoff⟩ := h
    have hd := hc.1 dst
    rw [hfp] at hd
    simp only [AVal.denote] at hd
    refine ⟨hc.1, fun hm x hx => ?_⟩
    show (writeByWidth s.mem _ val w).read x = _
    rw [writeByWidth_read_far _ _ _ _ _ (by
      rw [hd]; unfold effectiveAddr STACK_TOP; simp only [STACK_START, INPUT_START] at hx ⊢
      omega)]
    exact hc.2 hm x hx
  · exact ⟨hc.1, fun h => by cases h⟩

/-- **One step is sound.** A top-level step other than a call either leaves the state in
    place with the same registers and memory (a fault, or the final `exit`), or moves to a
    static successor satisfying the transferred abstract state. -/
theorem absStep_sound (s0 : State) (a : AState) (s : State) (insn : Insn)
    (hc : Concrete s0 a s) (hcs : s.callStack = []) (hnc : ∀ t, insn ≠ .call_local t)
    (hnx : ∀ r, insn ≠ .callx r) :
    ((step insn s).pc = s.pc ∧ Concrete s0 a (step insn s)) ∨
      ((step insn s).pc ∈ staticSucc s.pc insn ∧ Concrete s0 (absStep a insn) (step insn s)) := by
  cases insn
  case call_local t => exact absurd rfl (hnc t)
  case callx r => exact absurd rfl (hnx r)
  case exit =>
    left
    exact ⟨by simp [step, hcs], concrete_regs_mem hc (by simp [step, hcs]) (by simp [step, hcs])⟩
  case call sc =>
    right
    refine ⟨by simp [step, staticSucc], fun r => ?_, fun h => by cases h⟩
    cases r <;> simp only [absStep, AState.afterSyscall, AState.get, AVal.denote]
    show AVal.denote s0 a.r10 (execSyscall sc s).regs.r10
    rw [execSyscall_preserves_r10]
    exact hc.1 .r10
  case lddw dst imm =>
    right; exact ⟨by simp [step, staticSucc], concrete_set hc dst _ _ (fun _ => rfl) rfl rfl⟩
  case mov64 dst src =>
    right
    refine ⟨by simp [step, staticSucc], ?_⟩
    cases src with
    | imm i => exact concrete_set hc dst _ _ (fun _ => rfl) rfl rfl
    | reg r => exact concrete_set hc dst _ _ (fun _ => hc.1 r) rfl rfl
  case ldx w dst src off =>
    simp only [step]
    split
    · right
      exact ⟨by simp [staticSucc], concrete_set hc dst _ _
        (fun _ => ldx_value_sound s0 s a hc w src off) rfl rfl⟩
    · left; exact ⟨rfl, concrete_regs_mem hc rfl rfl⟩
  case st w dst off imm =>
    simp only [step]
    split
    · right; exact ⟨by simp [staticSucc], store_keeps s0 s a hc dst off _ w⟩
    · left; exact ⟨rfl, concrete_regs_mem hc rfl rfl⟩
  case stx w dst off src =>
    simp only [step]
    split
    · right; exact ⟨by simp [staticSucc], store_keeps s0 s a hc dst off _ w⟩
    · left; exact ⟨rfl, concrete_regs_mem hc rfl rfl⟩
  case ja t =>
    right; exact ⟨by simp [step, staticSucc], concrete_regs_mem hc rfl rfl⟩
  all_goals first
    | (right
       refine ⟨?_, concrete_regs_mem hc rfl rfl⟩
       simp only [step, staticSucc]; split <;> simp)
    | (right
       exact ⟨by simp [step, staticSucc], concrete_set hc _ _ .top (fun _ => trivial) rfl rfl⟩)
    | (simp only [step]
       split
       · left; exact ⟨rfl, concrete_regs_mem hc rfl rfl⟩
       · right
         exact ⟨by simp [staticSucc], concrete_set hc _ _ .top (fun _ => trivial) rfl rfl⟩)

/-! ## The abstract map and its check -/

def AVal.join (x y : AVal) : AVal := if x = y then x else .top

def AState.join (a b : AState) : AState :=
  { r0 := a.r0.join b.r0, r1 := a.r1.join b.r1, r2 := a.r2.join b.r2, r3 := a.r3.join b.r3,
    r4 := a.r4.join b.r4, r5 := a.r5.join b.r5, r6 := a.r6.join b.r6, r7 := a.r7.join b.r7,
    r8 := a.r8.join b.r8, r9 := a.r9.join b.r9, r10 := a.r10.join b.r10,
    memSame := a.memSame && b.memSame }

def allRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

/-- `c` is implied by `b`: every register `c` pins, `b` pins the same way. -/
def AState.le (b c : AState) : Bool :=
  allRegs.all (fun r => c.get r == .top || c.get r == b.get r) && (!c.memSame || b.memSame)

theorem concrete_le {s0 t : State} {b c : AState} (h : Concrete s0 b t)
    (hle : b.le c = true) : Concrete s0 c t := by
  simp only [AState.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hle
  obtain ⟨hregs, hmem⟩ := hle
  refine ⟨fun r => ?_, fun hc => ?_⟩
  · have := List.all_eq_true.mp hregs r (mem_allRegs r)
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h1 | h1 <;> rw [h1]
    · trivial
    · exact h.1 r
  · rcases hmem with h1 | h1
    · rw [h1] at hc; cases hc
    · exact h.2 h1

/-- Worklist fixpoint over the static CFG from `entry` (unverified: only `absCheck` is
    trusted). -/
def absMap (fetch : Nat → Option Insn) (noret : Nat → Bool) (size entry : Nat)
    (init : AState) : Array (Option AState) :=
  go ((Array.replicate size none).setIfInBounds entry (some init)) [entry] (size * 40)
where
  go (m : Array (Option AState)) (work : List Nat) : Nat → Array (Option AState)
    | 0 => m
    | fuel + 1 =>
      match work with
      | [] => m
      | p :: rest =>
        match m.getD p none, fetch p with
        | some a, some insn =>
          let out := absStep a insn
          let step := fun (acc : Array (Option AState) × List Nat) (q : Nat) =>
            if q < size then
              match acc.1.getD q none with
              | none => (acc.1.setIfInBounds q (some out), q :: acc.2)
              | some b =>
                let j := b.join out
                if j = b then acc else (acc.1.setIfInBounds q (some j), q :: acc.2)
            else acc
          let r := (callSucc noret p insn).foldl step (m, [])
          go r.1 (r.2 ++ rest) fuel
        | _, _ => go m rest fuel

/-- The map is a post-fixpoint: the entry covers `init`, no reachable `callx`, and every
    static edge's transferred state is covered at its target. -/
def absCheck (fetch : Nat → Option Insn) (noret : Nat → Bool) (m : Array (Option AState))
    (entry : Nat) (init : AState) : Bool :=
  (match m.getD entry none with | some e => init.le e | none => false) &&
  (List.range m.size).all fun pc =>
    match m.getD pc none with
    | none => true
    | some a =>
      match fetch pc with
      | none => true
      | some (.callx _) => false
      | some insn => (callSucc noret pc insn).all fun q =>
          match m.getD q none with
          | some b => (absStep a insn).le b
          | none => false

theorem absCheck_at {fetch : Nat → Option Insn} {noret : Nat → Bool}
    {m : Array (Option AState)} {entry : Nat} {init : AState}
    (h : absCheck fetch noret m entry init = true) {pc : Nat} {a : AState}
    (ha : m.getD pc none = some a) {insn : Insn} (hf : fetch pc = some insn) :
    (∀ r, insn ≠ .callx r) ∧ ∀ q ∈ callSucc noret pc insn,
      ∃ b, m.getD q none = some b ∧ (absStep a insn).le b = true := by
  simp only [absCheck, Bool.and_eq_true] at h
  have hlt : pc < m.size := by
    cases Nat.lt_or_ge pc m.size with
    | inl h => exact h
    | inr hge => simp [Array.getD, Nat.not_lt.mpr hge] at ha
  have := List.all_eq_true.mp h.2 pc (List.mem_range.mpr hlt)
  rw [ha, hf] at this
  cases insn
  case callx r => cases this
  all_goals
    refine ⟨(fun r h => by cases h), fun q hq => ?_⟩
    have hq' := List.all_eq_true.mp this q hq
    revert hq'
    cases hb : m.getD q none with
    | none => intro h; cases h
    | some b => intro h; exact ⟨b, rfl, h⟩

/-- **Abstract interpretation is sound.** If the check passes, every top-level state of a run
    from `s0` (at `entry`, empty stack, described by `init`) has an abstract state at its PC
    that describes it. -/
theorem abs_sound (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (m : Array (Option AState)) (entry : Nat)
    (init : AState) (hchk : absCheck fetch noret m entry init = true) (s0 : State)
    (hpc : s0.pc = entry) (hcs : s0.callStack = []) (hinit : Concrete s0 init s0) (n : Nat)
    (hend : (executeFn fetch s0 n).callStack = []) :
    ∃ a, m.getD (executeFn fetch s0 n).pc none = some a ∧ Concrete s0 a (executeFn fetch s0 n) := by
  refine inv_holds fetch noret hNR (fun s => ∃ a, m.getD s.pc none = some a ∧ Concrete s0 a s)
    ?_ ?_ ?_ ?_ n s0 hcs ?_ hend
  · intro s e v ⟨a, ha, hc⟩; exact ⟨a, ha, concrete_regs_mem hc rfl rfl⟩
  · intro s insn hcs' _ ⟨a, ha, hc⟩ hf hnc hnx
    obtain ⟨_, hsucc⟩ := absCheck_at hchk ha hf
    rcases absStep_sound s0 a s insn hc hcs' hnc hnx with ⟨hp, hc'⟩ | ⟨hp, hc'⟩
    · exact ⟨a, by show m.getD (step insn s).pc none = _; rw [hp]; exact ha,
        concrete_regs_mem hc' rfl rfl⟩
    · obtain ⟨b, hb, hle⟩ := hsucc _ (by rw [callSucc_of_not_call noret _ insn hnc]; exact hp)
      exact ⟨b, hb, concrete_regs_mem (concrete_le hc' hle) rfl rfl⟩
  · intro s r _ ⟨a, ha, _⟩ hf
    exact (absCheck_at hchk ha hf).1 r rfl
  · intro s t _ _ ⟨a, ha, hc⟩ hf hnr u _ hu2 hu6 hu7 hu8 hu9 hu10 _
    obtain ⟨_, hsucc⟩ := absCheck_at hchk ha hf
    obtain ⟨b, hb, hle⟩ := hsucc (s.pc + 1) (by simp [callSucc, hnr])
    refine ⟨b, by rw [hu2]; exact hb, concrete_le ⟨fun r => ?_, fun h => by cases h⟩ hle⟩
    cases r <;> simp only [absStep, AState.afterCall, AState.get, AVal.denote] <;>
      first
      | trivial
      | (show AVal.denote s0 a.r6 u.regs.r6; rw [hu6]; exact hc.1 .r6)
      | (show AVal.denote s0 a.r7 u.regs.r7; rw [hu7]; exact hc.1 .r7)
      | (show AVal.denote s0 a.r8 u.regs.r8; rw [hu8]; exact hc.1 .r8)
      | (show AVal.denote s0 a.r9 u.regs.r9; rw [hu9]; exact hc.1 .r9)
      | (show AVal.denote s0 a.r10 u.regs.r10; rw [hu10]; exact hc.1 .r10)
  · simp only [absCheck, Bool.and_eq_true] at hchk
    have h1 := hchk.1
    revert h1
    cases he : m.getD entry none with
    | none => intro h; cases h
    | some e => intro h; exact ⟨e, by rw [hpc]; exact he, concrete_le hinit h⟩

end SVM.SBPF
