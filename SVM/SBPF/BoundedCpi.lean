/-
  Boundedness on the runtime stepper (`executeFnCpi` / `Runner.run`).

  `executeFn_bounded` (Bounded.lean) shows the SPEC stepper preserves
  `StateBounded` (L5/L3). The runtime path uses `executeFnCpi`; for a
  CPI-FREE program the two coincide (`executeFnCpi_eq_executeFn_of_no_cpi`),
  so boundedness transfers verbatim. This file states that transfer as a
  named theorem — the L5/L3 closure on the ACTUAL runtime path for the
  realistic class (every current lift is CPI-free).

  Boundedness ACROSS an actual CPI call (the recursive sub-VM + write-back)
  is the Stage-B chain below: `cpiCallNextState_bounded` (the commit step) →
  `buildCalleeVM_bounded` (the fresh sub-VM state) →
  `executeFnCpiWithFuel_bounded` (the fuel induction, closing `hcallee`) →
  `run_bounded` (end-to-end on `Runner.run`, CPI or not). The two remaining
  named black boxes are hypotheses of the wrapper: `hnative` (per-native-
  handler byte-boundedness) and `hexit` (the per-`step` exit-code sweep) —
  the staged backlog; see docs/PHASE7_LIFT_HARDENING_PLAN.md.
-/

import SVM.SBPF.Bounded
import SVM.SBPF.RunnerBridge

namespace SVM.SBPF

open Memory

/-- The runtime stepper preserves `StateBounded` on a CPI-free program:
    `executeFnCpi` coincides with the spec stepper there and `executeFn_bounded`
    closes it. So L5/L3 hold along the genuine runtime trace, not just the
    `cuTripleWithin` `executeFn` trace the lifts reason over. -/
theorem executeFnCpi_bounded_of_no_cpi
    (registry : Nat → Option ByteArray) (fetch : Nat → Option Insn)
    {s : State} (hb : StateBounded s) (fuel : Nat)
    (hnc : ∀ a i, fetch a = some i → Insn.isCpiCall i = false) :
    StateBounded (Runner.executeFnCpi registry fetch s fuel) := by
  rw [Runner.executeFnCpi_eq_executeFn_of_no_cpi registry fetch s fuel hnc]
  exact executeFn_bounded fetch hb fuel

/-- End-to-end runtime boundedness for a CPI-free program: `Runner.run`
    succeeds with a `StateBounded` final state. The budget bound
    `cfg.cuBudget < 2^64` holds on every real run (the FFI passes a u64). -/
theorem run_bounded_of_no_cpi {bs : ByteArray} {cfg : Runner.RunConfig}
    {insns : Array Insn}
    (hdecode : Decode.decodeProgram bs [(Elf.entrypointHash, 0)] = some insns)
    (hnoCpi : ∀ i, i ∈ insns → Insn.isCpiCall i = false)
    (hcu : cfg.cuBudget < U64_MODULUS) :
    ∃ sf, Runner.run bs cfg = some sf ∧ StateBounded sf := by
  refine ⟨Runner.executeFnCpi cfg.programRegistry (Runner.fetchFromArray insns)
            (Runner.initialState cfg) cfg.cuBudget, ?_, ?_⟩
  · simp only [Runner.run, hdecode, bind, Option.bind, pure]
  · exact executeFnCpi_bounded_of_no_cpi _ _ (initialState_bounded cfg hcu) _
      (Runner.fetchFromArray_property_of_mem hnoCpi)

/-! ## Boundedness ACROSS a CPI call (Phase 7 sub-item 4, Stage B)

The cross-CPI gap. `cpiCallNextState` clamps privileges (C5), detects writable
aliasing (#8), dispatches to a native handler or recursive BPF sub-VM, and
commits the result (the M6r realloc-harvest write-back). This section proves
that commit step preserves `StateBounded`, reduced to the two semantic black
boxes it calls into:

- `hnative` — a native handler returns a u64 `r0` + byte-bounded memory; the
  long-pole backlog (per-handler).
- `hcallee` — the recursive sub-VM result is u64/byte/cap-bounded; discharged
  at the `executeFnCpiWithFuel` level by the fuel induction + write-back fold,
  left as a hypothesis here so this lemma is independent of the recursion.

The `executeFnCpiWithFuel_bounded` wrapper is the remaining Stage-B work; see
docs/PHASE7_LIFT_HARDENING_PLAN.md. -/

/-- CPI dispatch arms 1/2/4a/4b — depth-limit / writable-alias / unknown
    registry / failed sub-load — all return `{ s with r0 := 1, pc, cu }`.
    `StateBounded` ignores `pc`/`cuConsumed`; `set .r0` cannot touch r10. -/
theorem StateBounded.with_cpi_r0 {s : State} (h : StateBounded s)
    {r0v : Nat} (hr0 : r0v < U64_MODULUS) (pc' cu' : Nat) :
    StateBounded { s with regs := s.regs.set .r0 r0v, pc := pc',
                          cuConsumed := cu' } :=
  { regs_lt := RegFile.set_get_lt h.regs_lt hr0 .r0
    stack_r10 := by
      show StackR10WF s.callStack (s.regs.set .r0 r0v).r10
      rw [RegFile.set_preserves_r10]; exact h.stack_r10
    stack_depth := h.stack_depth
    frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt
    heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le
    mem_lt := h.mem_lt }

/-- CPI dispatch arm 3 — native handler success: `with_cpi_r0` plus a fresh
    memory (byte-bounded by `hnative`). -/
theorem StateBounded.with_cpi_r0_mem {s : State} (h : StateBounded s)
    {r0v : Nat} (hr0 : r0v < U64_MODULUS) {m' : Mem} (hm : ∀ a, m' a < 256)
    (pc' cu' : Nat) :
    StateBounded { s with regs := s.regs.set .r0 r0v, mem := m', pc := pc',
                          cuConsumed := cu' } :=
  { regs_lt := RegFile.set_get_lt h.regs_lt hr0 .r0
    stack_r10 := by
      show StackR10WF s.callStack (s.regs.set .r0 r0v).r10
      rw [RegFile.set_preserves_r10]; exact h.stack_r10
    stack_depth := h.stack_depth
    frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt
    heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le
    mem_lt := hm }

/-- CPI dispatch arm 4c — recursive BPF sub-VM success: surfaced exit code is
    u64, return-data within the agave cap, written-back caller memory
    byte-bounded (all from `hcallee`); stack/budget/heap untouched. -/
theorem StateBounded.with_cpi_commit {s : State} (h : StateBounded s)
    {r0v : Nat} (hr0 : r0v < U64_MODULUS) {m' : Mem} (hm : ∀ a, m' a < 256)
    {rd : ByteArray} (hrd : rd.size ≤ 1024)
    (pc' cu' : Nat) (lg : Array ByteArray) (rdp : ByteArray) :
    StateBounded { s with regs := s.regs.set .r0 r0v, mem := m', pc := pc',
                          log := lg, returnData := rd, returnDataProgId := rdp,
                          cuConsumed := cu' } :=
  { regs_lt := RegFile.set_get_lt h.regs_lt hr0 .r0
    stack_r10 := by
      show StackR10WF s.callStack (s.regs.set .r0 r0v).r10
      rw [RegFile.set_preserves_r10]; exact h.stack_r10
    stack_depth := h.stack_depth
    frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt
    heapNext_le := h.heapNext_le
    returnData_le := hrd
    mem_lt := hm }

/-- The CPI commit step preserves `StateBounded`. Each `cpiCallNextState`
    outcome is a `with_cpi_*`-shaped record update; the foreign-data arms
    (native handler 3, sub-VM 4c) get their bounds from `hnative` / `hcallee`.
    The privilege-clamp / alias-detection bookkeeping touches no `StateBounded`
    component.

    `hsc` restricts to the two invoke syscalls — the only ones routed through
    this helper — so the ABI-dependent `match sc` lets reduce to concrete
    bodies and `split` sees only the five real branches. -/
theorem cpiCallNextState_bounded
    (registry : Nat → Option ByteArray) {s : State} {sc : Syscall} (fuel' : Nat)
    (runCallee : ByteArray → Option (State × Mem × Nat)) (h : StateBounded s)
    (hsc : sc = Syscall.sol_invoke_signed ∨ sc = Syscall.sol_invoke_signed_c)
    (hnative : ∀ (pid : Nat) (ixData : ByteArray) (accts : List Native.AcctInput)
        (nr : Native.NativeResult),
        Native.dispatch pid ixData accts s.mem = some nr →
          nr.r0 < U64_MODULUS ∧ ∀ a, nr.mem a < 256)
    (hcallee : ∀ (elf : ByteArray) (subFinal : State) (newMem : Mem) (fr : Nat),
        runCallee elf = some (subFinal, newMem, fr) →
          subFinal.exitCode.getD 1 < U64_MODULUS ∧
          subFinal.returnData.size ≤ 1024 ∧ ∀ a, newMem a < 256) :
    StateBounded (Runner.cpiCallNextState registry s sc fuel' runCallee) := by
  -- `extract_lets` lifts the heavy lets (pid fold, account parsers, ABI
  -- `match sc`) into the context WITHOUT evaluating them (avoids a >150s simp
  -- blowup) so `split` can see the structural branches; each arm closes by a
  -- `with_cpi_*` shape, native / sub-VM arms via `hnative` / `hcallee`.
  rcases hsc with rfl | rfl <;>
    (unfold Runner.cpiCallNextState
     extract_lets
     repeat' split
     all_goals
       first
         -- arms 1 / 2 / 4a / 4b — `{ s with r0 := 1, pc, cu }`
         | exact h.with_cpi_r0 (r0v := 1) (by decide) _ _
         -- arm 3 — native handler success (`hnative`)
         | (obtain ⟨hr0, hmem⟩ :=
              hnative _ _ _ _ ‹Native.dispatch _ _ _ s.mem = some _›
            exact h.with_cpi_r0_mem hr0 hmem _ _)
         -- arm 4c — recursive sub-VM commit (`hcallee`)
         | (obtain ⟨hexit, hrd, hmem⟩ :=
              hcallee _ _ _ _ ‹runCallee _ = some _›
            exact h.with_cpi_commit hexit hmem hrd _ _ _ _))

/-- `Memory.writeU64` preserves byte-boundedness (defeq to `writeByWidth …
    .dword`). The CPI write-back's length/lamport dual-writes go through it. -/
theorem writeU64_lt (m : Mem) (addr v : Nat) (h : ∀ a, m a < 256) :
    ∀ a, (Memory.writeU64 m addr v) a < 256 :=
  writeByWidth_lt m addr v .dword h

/-- The CPI commit never touches `exitCode` (every `cpiCallNextState` arm
    preserves it, for ANY `sc`), so the wrapper's exit-code co-invariant
    carries across a CPI call for free. -/
theorem cpiCallNextState_exitCode (registry : Nat → Option ByteArray)
    (s : State) (sc : Syscall) (fuel' : Nat)
    (runCallee : ByteArray → Option (State × Mem × Nat)) :
    (Runner.cpiCallNextState registry s sc fuel' runCallee).exitCode = s.exitCode := by
  unfold Runner.cpiCallNextState
  extract_lets
  repeat' split
  all_goals rfl

/-! ## `commitCallee` / `buildCalleeVM` boundedness (Stage B wrapper supports)

With `runCallee` factored into `buildCalleeVM` (pre-build) and `commitCallee`
(write-back), the cross-CPI `hcallee` obligation reduces to named facts about
those two. -/

/-- A `List.foldl` whose step preserves byte-boundedness preserves it overall —
    generic core behind the CPI write-back fold. -/
theorem foldl_mem_lt {α : Type} (f : Mem → α → Mem) (l : List α) (m0 : Mem)
    (hf : ∀ (m : Mem) (x : α), (∀ a, m a < 256) → ∀ a, f m x a < 256)
    (h0 : ∀ a, m0 a < 256) : ∀ a, (l.foldl f m0) a < 256 := by
  induction l generalizing m0 with
  | nil => exact h0
  | cons x rest ih => exact ih (f m0 x) (hf m0 x h0)

/-- `commitCallee` preserves L3 byte-boundedness: violations return caller
    memory unchanged; the honest path folds writable accounts back via
    `loadBytesAt` + `writeU64` (both byte-reducing). -/
theorem commitCallee_mem_lt (callerMem : Mem) (slots : List Runner.AcctSlot)
    (subFinal : State) (fr : Nat) (h : ∀ a, callerMem a < 256) :
    ∀ a, (Runner.commitCallee callerMem slots subFinal fr).2.1 a < 256 := by
  unfold Runner.commitCallee
  extract_lets roV reV nwm
  have hnwm : ∀ a, nwm a < 256 := by
    apply foldl_mem_lt _ _ _ ?_ h
    intro m slot hm a
    dsimp only
    split
    · exact hm a
    · split
      · exact hm a
      · exact loadBytesAt_lt _ _ _
          (writeU64_lt _ _ _ (writeU64_lt _ _ _ (writeU64_lt _ _ _
            (loadBytesAt_lt _ _ _ hm)))) a
  intro a
  split
  · exact h a
  · split
    · exact h a
    · exact hnwm a

/-- `commitCallee` keeps the sub-VM's return-data buffer, so the agave
    1024-byte cap carries. -/
theorem commitCallee_returnData (callerMem : Mem) (slots : List Runner.AcctSlot)
    (subFinal : State) (fr : Nat) :
    (Runner.commitCallee callerMem slots subFinal fr).1.returnData =
      subFinal.returnData := by
  unfold Runner.commitCallee
  extract_lets
  repeat' split
  all_goals rfl

/-- `commitCallee`'s surfaced exit code is u64 whenever the sub-VM's is: a
    violation surfaces a fixed `ERR_*` sentinel, the honest path passes
    `subFinal.exitCode` through. -/
theorem commitCallee_exitCode_lt (callerMem : Mem) (slots : List Runner.AcctSlot)
    (subFinal : State) (fr : Nat) (h : subFinal.exitCode.getD 1 < U64_MODULUS) :
    (Runner.commitCallee callerMem slots subFinal fr).1.exitCode.getD 1
      < U64_MODULUS := by
  unfold Runner.commitCallee
  extract_lets
  split
  · show ERR_INVALID_REALLOC < U64_MODULUS
    decide
  · split
    · show ERR_READONLY_MODIFIED < U64_MODULUS
      decide
    · exact h

/-! ## `buildCalleeVM` boundedness -/

/-- The fresh CPI sub-VM state record is bounded: fresh registers (only
    r1/r10 set, r10 at the empty-stack frame base), empty call stack,
    `cuBudget := fuel'`, default heap pointer, inherited return-data. -/
theorem StateBounded.cpi_sub (s : State) (m : Mem) (rt : Memory.RegionTable)
    (pcv : Nat) (pid : ByteArray) (privs : List (ByteArray × Bool × Bool))
    (fuel' : Nat) (hm : ∀ a, m a < 256) (hfuel : fuel' < U64_MODULUS)
    (hrd : s.returnData.size ≤ 1024) :
    StateBounded { regs := { r1 := INPUT_START, r10 := STACK_START + 0x1000 },
                   mem := m, regions := rt, pc := pcv, log := s.log,
                   returnData := s.returnData,
                   returnDataProgId := s.returnDataProgId,
                   cuBudget := fuel', progIdBytes := pid, origPrivs := privs,
                   invokeDepth := s.invokeDepth + 1 } :=
  { regs_lt := by intro r; cases r <;> simp [RegFile.get, U64_MODULUS] <;> decide
    stack_r10 := rfl
    stack_depth := by show List.length [] ≤ MAX_CALL_DEPTH; decide
    frames_lt := by intro f hf; cases hf
    cuBudget_lt := hfuel
    heapNext_le := by show (0x300000000 : Nat) ≤ 0x300008000; decide
    returnData_le := hrd
    mem_lt := hm }

-- Failed unification against the opaque `baseMem` below must not whnf the
-- loader/parser bodies (foldls over abstract byte arrays) — seal them for
-- the peeling proofs. `seal` is file-local, so importers are unaffected.
seal Runner.loadBytesAt Runner.loadInput Runner.buildCpiSubInputN
seal Elf.extractSection Elf.applyRelocations Elf.applyDataRelocations
seal Elf.parseHeader Elf.findSection Elf.buildFnRegistry Decode.decodeProgram

/-- `buildCalleeVM` only ever launches a bounded, still-running sub-VM: the
    fresh sub-state is `StateBounded` (its memory is the loaded input image
    plus `.text`/`.rodata`/`.data.rel.ro` section loads — all byte-real) with
    `exitCode = none`. `hfuel` bounds the sub-VM's `cuBudget := fuel'`;
    `hrd` carries the caller's return-data cap into the inherited buffer. -/
theorem buildCalleeVM_bounded {s : State} {fuel' : Nat}
    {pidBytesIn : ByteArray} {parsedAcctsIn : List Runner.ParsedAcct}
    {ixDataIn calleeBytes : ByteArray}
    {ci : Array Insn} {ss : State} {sl : List Runner.AcctSlot}
    (heq : Runner.buildCalleeVM s fuel' pidBytesIn parsedAcctsIn ixDataIn
      calleeBytes = some (ci, ss, sl))
    (hfuel : fuel' < U64_MODULUS) (hrd : s.returnData.size ≤ 1024) :
    StateBounded ss ∧ ss.exitCode = none := by
  unfold Runner.buildCalleeVM at heq
  extract_lets tryElf slots subInput baseMem jp at heq
  have hbase : ∀ a, baseMem a < 256 := loadInput_lt _
  -- Make the heavy ELF-parse terms opaque: every later step is structural
  -- (case split / head-symbol match), so defeq must not unfold them.
  clear_value tryElf slots subInput baseMem
  -- Peel the M1/H2 guard prelude to quiescence: guards reduce to ifs via the
  -- simp set, `split` cases them, dead branches (`none = some _`) die by
  -- ctor clash. Every survivor funnels into the join point `jp`.
  repeat'
    first
      | contradiction
      | split at heq
      | simp only [guard, bind, pure, Option.bind,
          show (failure : Option Unit) = none from rfl] at heq
  -- Every survivor is `jp _ = some (ci, ss, sl)`: unfold the join point and
  -- split its body (tryElf tuple destructure, decodeProgram bind) the same way.
  all_goals simp only [jp, bind, Option.bind] at heq
  repeat'
    first
      | contradiction
      | split at heq
  -- Every survivor is `some (ci', subS, slots) = some (ci, ss, sl)`.
  all_goals simp only [Option.some.injEq, Prod.mk.injEq] at heq
  all_goals obtain ⟨-, hss, -⟩ := heq
  all_goals subst hss
  all_goals refine ⟨StateBounded.cpi_sub _ _ _ _ _ _ _ ?_ hfuel hrd, rfl⟩
  -- Each remaining goal is `∀ a, (loadBytesAt-chain over baseMem) a < 256`:
  -- peel one loader per step down to the input image.
  all_goals
    repeat first
      | exact hbase
      | (refine loadBytesAt_lt _ _ _ ?_)

/-! ## The Stage-B wrapper: boundedness through `executeFnCpiWithFuel` -/

/-- Exit-code co-invariant carried through the fuel induction: any surfaced
    exit code is a real u64. Needed because a CPI caller writes the callee's
    `exitCode.getD 1` into `r0` (`with_cpi_commit`'s `hr0`). -/
def exitBounded (s : State) : Prop :=
  ∀ v, s.exitCode = some v → v < U64_MODULUS

theorem exitBounded.getD_lt {s : State} (h : exitBounded s) :
    s.exitCode.getD 1 < U64_MODULUS := by
  cases hex : s.exitCode with
  | none => decide
  | some v => exact h v hex

/-- THE cross-CPI preservation theorem: the runtime stepper keeps every
    reachable state `StateBounded` (with u64 exit codes), through any depth
    of recursive CPI sub-VMs — the L5/L3 closure on the actual runtime path,
    no CPI-free restriction.

    A plain induction on fuel covers both the tail and the sub-VM (both
    recurse at `fuel'`); the CPI commit arm reduces to
    `cpiCallNextState_bounded`, whose `hcallee` obligation is discharged by
    `buildCalleeVM_bounded` (fresh sub-state bounded) + the induction
    hypothesis (sub-VM run bounded) + the `commitCallee_*` write-back lemmas.

    Two named black boxes stay hypotheses (the staged backlog,
    docs/PHASE7_LIFT_HARDENING_PLAN.md):
    - `hnative`: a native handler returns a u64 `r0` and byte-bounded memory
      (per-handler sweep over `Native.dispatch`);
    - `hexit`: `step` only surfaces u64 exit codes (per-arm sweep mirroring
      `step_bounded`). -/
theorem executeFnCpiWithFuel_bounded (registry : Nat → Option ByteArray)
    (hnative : ∀ (pid : Nat) (ixData : ByteArray)
        (accts : List Native.AcctInput) (m : Mem), (∀ a, m a < 256) →
        ∀ nr, Native.dispatch pid ixData accts m = some nr →
          nr.r0 < U64_MODULUS ∧ ∀ a, nr.mem a < 256)
    (hexit : ∀ (insn : Insn) (s : State), StateBounded s → exitBounded s →
        exitBounded (step insn s)) :
    ∀ (fuel : Nat) (fetch : Nat → Option Insn) (s : State),
      fuel < U64_MODULUS → StateBounded s → exitBounded s →
      StateBounded (Runner.executeFnCpiWithFuel registry fetch s fuel).1 ∧
      exitBounded (Runner.executeFnCpiWithFuel registry fetch s fuel).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro fetch s _ hb he
    exact ⟨hb, he⟩
  | succ fuel' ih =>
    intro fetch s hfuel hb he
    have hfuel' : fuel' < U64_MODULUS := Nat.lt_of_succ_lt hfuel
    cases hex : s.exitCode with
    | some v =>
      simp only [Runner.executeFnCpiWithFuel, hex]
      exact ⟨hb, he⟩
    | none =>
      by_cases hover : s.cuConsumed > s.cuBudget
      · simp only [Runner.executeFnCpiWithFuel, hex, if_pos hover]
        exact ⟨hb, he⟩
      · cases hf : fetch s.pc with
        | none =>
          simp only [Runner.executeFnCpiWithFuel, hex, if_neg hover, hf]
          refine ⟨hb.with_abort _ _, ?_⟩
          intro v hv
          obtain rfl : ERR_INVALID_PC = v := by simpa using hv
          decide
        | some insn =>
          simp only [Runner.executeFnCpiWithFuel, hex, if_neg hover, hf,
            Runner.traceStep, Runner.TRACE_STEPS, Bool.false_eq_true, if_false]
          -- The recursive-callee discharge (`hcallee`), uniform across both
          -- CPI ABIs: peel `buildCalleeVM` (bounded fresh sub-state), run the
          -- fuel IH on the sub-VM, carry the result through `commitCallee`.
          have hrc : ∀ (pidB : ByteArray) (pAccts : List Runner.ParsedAcct)
              (ixD elf : ByteArray) (subFinal : State) (newMem : Mem) (fr : Nat),
              (do
                let (calleeInsns, subS, slots) ←
                  Runner.buildCalleeVM s fuel' pidB pAccts ixD elf
                let (subF, sfr) := Runner.executeFnCpiWithFuel registry
                  (Runner.fetchFromArray calleeInsns) subS fuel'
                some (Runner.commitCallee s.mem slots subF sfr))
                = some (subFinal, newMem, fr) →
              subFinal.exitCode.getD 1 < U64_MODULUS ∧
              subFinal.returnData.size ≤ 1024 ∧ ∀ a, newMem a < 256 := by
            intro pidB pAccts ixD elf subFinal newMem fr heq
            cases hbuild : Runner.buildCalleeVM s fuel' pidB pAccts ixD elf with
            | none =>
              rw [hbuild] at heq
              simp only [bind, Option.bind] at heq
              exact nomatch heq
            | some t =>
              obtain ⟨ci', ss', sl'⟩ := t
              rw [hbuild] at heq
              obtain ⟨hbss, hssex⟩ :=
                buildCalleeVM_bounded hbuild hfuel' hb.returnData_le
              obtain ⟨hsfb, hsfe⟩ := ih (Runner.fetchFromArray ci') ss' hfuel'
                hbss (by intro v hv; rw [hssex] at hv; cases hv)
              cases hrun : Runner.executeFnCpiWithFuel registry
                  (Runner.fetchFromArray ci') ss' fuel' with
              | mk subF sfr =>
                rw [hrun] at hsfb hsfe
                simp only [bind, Option.bind, hrun, Option.some.injEq] at heq
                have h1 : (Runner.commitCallee s.mem sl' subF sfr).1 = subFinal := by
                  rw [heq]
                refine ⟨?_, ?_, ?_⟩
                · rw [← h1]
                  exact commitCallee_exitCode_lt _ _ _ _ hsfe.getD_lt
                · rw [← h1, commitCallee_returnData]
                  exact hsfb.returnData_le
                · intro a
                  have h3 : (Runner.commitCallee s.mem sl' subF sfr).2.1 = newMem := by
                    rw [heq]
                  rw [← h3]
                  exact commitCallee_mem_lt _ _ _ _ hb.mem_lt a
          refine ih fetch _ hfuel' ?_ ?_
          · -- `StateBounded (chargeCu s')`: the three instruction classes.
            refine chargeCu_bounded ?_
            split
            · exact cpiCallNextState_bounded registry fuel' _ hb (Or.inl rfl)
                (fun pid ixd accts nr hd =>
                  hnative pid ixd accts s.mem hb.mem_lt nr hd)
                (fun elf subF nm fr h => hrc _ _ _ elf subF nm fr h)
            · exact cpiCallNextState_bounded registry fuel' _ hb (Or.inr rfl)
                (fun pid ixd accts nr hd =>
                  hnative pid ixd accts s.mem hb.mem_lt nr hd)
                (fun elf subF nm fr h => hrc _ _ _ elf subF nm fr h)
            · exact step_bounded _ hb
          · -- `exitBounded (chargeCu s')`: CPI arms keep `exitCode = none`
            -- (`cpiCallNextState_exitCode`); the step arm is `hexit`.
            intro v hv
            split at hv
            · rw [show ∀ x : State, (chargeCu x).exitCode = x.exitCode
                    from fun _ => rfl,
                  cpiCallNextState_exitCode, hex] at hv
              cases hv
            · rw [show ∀ x : State, (chargeCu x).exitCode = x.exitCode
                    from fun _ => rfl,
                  cpiCallNextState_exitCode, hex] at hv
              cases hv
            · exact hexit _ s hb he v hv

/-- End-to-end runtime boundedness, CPI or not: `Runner.run` succeeds with a
    `StateBounded` final state carrying a u64 exit code. The across-CPI
    counterpart of `run_bounded_of_no_cpi` (which needs neither `hnative`
    nor `hexit` but forbids CPI instructions). -/
theorem run_bounded {bs : ByteArray} {cfg : Runner.RunConfig}
    {insns : Array Insn}
    (hnative : ∀ (pid : Nat) (ixData : ByteArray)
        (accts : List Native.AcctInput) (m : Mem), (∀ a, m a < 256) →
        ∀ nr, Native.dispatch pid ixData accts m = some nr →
          nr.r0 < U64_MODULUS ∧ ∀ a, nr.mem a < 256)
    (hexit : ∀ (insn : Insn) (s : State), StateBounded s → exitBounded s →
        exitBounded (step insn s))
    (hdecode : Decode.decodeProgram bs [(Elf.entrypointHash, 0)] = some insns)
    (hcu : cfg.cuBudget < U64_MODULUS) :
    ∃ sf, Runner.run bs cfg = some sf ∧ StateBounded sf ∧ exitBounded sf := by
  refine ⟨Runner.executeFnCpi cfg.programRegistry (Runner.fetchFromArray insns)
            (Runner.initialState cfg) cfg.cuBudget, ?_, ?_⟩
  · simp only [Runner.run, hdecode, bind, Option.bind, pure]
  · exact executeFnCpiWithFuel_bounded cfg.programRegistry hnative hexit
      cfg.cuBudget (Runner.fetchFromArray insns) (Runner.initialState cfg) hcu
      (initialState_bounded cfg hcu)
      (by intro v hv; rw [Runner.initialState_exitCode] at hv; cases hv)

end SVM.SBPF
