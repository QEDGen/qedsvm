/-
  Boundedness on the runtime stepper (`executeFnCpi` / `Runner.run`).

  `executeFn_bounded` (Bounded.lean) shows the SPEC stepper preserves the
  `StateBounded` invariant (the L5/L3 closures). The actual runtime path
  (`Runner.run` / `runElf`) uses `executeFnCpi`, which additionally handles
  cross-program invocation. For a CPI-FREE program the two steppers coincide
  (`executeFnCpi_eq_executeFn_of_no_cpi`, RunnerBridge.lean), so boundedness
  transfers verbatim. This file states that transfer as a named, citable
  theorem: the L5/L3 closure on the ACTUAL runtime path for the realistic
  class — every current lift is CPI-free.

  Boundedness ACROSS an actual CPI call — `executeFnCpiWithFuel`'s
  `sol_invoke_signed[_c]` arm builds a fresh sub-state, runs the callee in a
  recursive sub-VM, and commits the result via `cpiCallNextState`'s write-back
  — is the remaining `StateBounded`-through-CPI work (Phase 7 sub-item 4,
  Stage B). It needs (1) `subS` bounded (fresh constant regs + `loadInput`
  mem, both already covered by `initState_bounded` / `loadInput_lt`),
  (2) strong fuel induction feeding the sub-VM result back through
  (3) `cpiCallNextState_bounded` (4 arms: depth-limit / alias / native /
  registry-callee), whose long pole is a per-handler `Native.dispatch`
  mem bound. See docs/PHASE7_LIFT_HARDENING_PLAN.md.
-/

import SVM.SBPF.Bounded
import SVM.SBPF.RunnerBridge

namespace SVM.SBPF

open Memory

/-- The runtime stepper preserves `StateBounded` on a CPI-free program:
    `executeFnCpi` coincides with the spec stepper `executeFn` there
    (`executeFnCpi_eq_executeFn_of_no_cpi`), and `executeFn_bounded` closes it.
    So every register stays a real u64 (L5) and every memory cell a real byte
    (L3) along the genuine runtime trace — not just the `cuTripleWithin`
    `executeFn` trace the lifts reason over. -/
theorem executeFnCpi_bounded_of_no_cpi
    (registry : Nat → Option ByteArray) (fetch : Nat → Option Insn)
    {s : State} (hb : StateBounded s) (fuel : Nat)
    (hnc : ∀ a i, fetch a = some i → Insn.isCpiCall i = false) :
    StateBounded (Runner.executeFnCpi registry fetch s fuel) := by
  rw [Runner.executeFnCpi_eq_executeFn_of_no_cpi registry fetch s fuel hnc]
  exact executeFn_bounded fetch hb fuel

/-- End-to-end runtime boundedness for a CPI-free program: `Runner.run`
    succeeds and its final state is `StateBounded`. Mirrors the
    `hdecode`/`hnoCpi` hypothesis shape of `RunnerBridge`'s end-to-end
    theorems; the budget bound `cfg.cuBudget < 2^64` is every real run (the
    FFI passes a u64). -/
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

The genuine cross-CPI gap. `executeFnCpiWithFuel`'s `sol_invoke_signed[_c]`
arm delegates its state transition to `Runner.cpiCallNextState`, which:
clamps account privileges (C5), detects writable aliasing (#8), dispatches
to a native handler or a recursive BPF sub-VM, and commits the result back
(the M6r realloc-harvest write-back). This section proves that commit step
preserves the `StateBounded` invariant (L5 register-faithfulness + L3
byte-faithfulness), reduced to the two genuinely-semantic black boxes it
calls into:

- `hnative` — a native handler returns a u64 `r0` and byte-bounded memory.
  Per-handler (`System` / `ComputeBudget` / `BpfLoaderUpgradeable` /
  precompiles); the long-pole backlog.
- `hcallee` — the recursive sub-VM result: its surfaced exit code is a u64,
  its return-data is within the agave cap, and the written-back caller
  memory is byte-bounded. Discharged at the `executeFnCpiWithFuel` level by
  the fuel induction (`StateBounded subFinal` from the IH) + the write-back
  fold lemma; left as a hypothesis here so the commit-step lemma is
  independent of the recursion.

The `executeFnCpiWithFuel_bounded` wrapper (strong fuel induction + the
fresh sub-state base case + the write-back fold + an exit-code soundness
sweep mirroring the `execSyscall_regs_lt`/`_mem_lt` discipline) is the
remaining Stage-B work; see docs/PHASE7_LIFT_HARDENING_PLAN.md. -/

/-- CPI dispatch arms 1/2/4a/4b — depth-limit, writable-alias, unknown
    registry, and failed sub-load — all return `{ s with r0 := 1, pc, cu }`.
    Register-write shape that also moves the CU meter; `StateBounded` ignores
    `pc`/`cuConsumed`, so this carries every component the way
    `StateBounded.with_set_reg` does (`set .r0` cannot touch r10). -/
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

/-- CPI dispatch arm 3 — native handler success: `{ s with r0 := nr.r0,
    mem := nr.mem, pc, cu }`. Same as `with_cpi_r0` plus a fresh memory
    (byte-bounded by `hnative`). -/
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

/-- CPI dispatch arm 4c — recursive BPF sub-VM success: `{ s with
    r0 := subFinal.exitCode.getD 1, mem := newMem, pc, log, returnData,
    returnDataProgId, cu }`. The surfaced exit code is a u64 and the
    return-data stays within the agave cap (`hcallee`); the written-back
    caller memory is byte-bounded (`hcallee`). The stack/budget/heap
    components are the caller's, untouched. -/
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

/-- The CPI commit step preserves `StateBounded`. Every one of
    `cpiCallNextState`'s four outcomes is a register/memory record update of
    a `with_cpi_*` shape; the two arms that pull in foreign data — the native
    handler (arm 3) and the recursive sub-VM (arm 4c) — get their u64/byte
    bounds from `hnative` / `hcallee`. The privilege-clamp / alias-detection
    bookkeeping ahead of the branch does not touch any `StateBounded`
    component.

    `hsc` restricts to the two invoke syscalls — the only ones
    `executeFnCpiWithFuel` ever routes through this helper (Runner.lean) — so
    the ABI-dependent `match sc` lets reduce to concrete bodies and `split`
    sees only the five real branches. -/
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
  -- `unfold` exposes the body; `extract_lets` lifts the heavy lets (the pid
  -- `List.range 32` fold, the recursive account parsers, the ABI `match sc`)
  -- into the context as local defs — WITHOUT evaluating them (so no >150s simp
  -- blowup) and so `split` can see the five structural branches (it does not
  -- descend through the let wrapper otherwise). `repeat' split` then exposes
  -- six clean arm records, each closed by a `with_cpi_*` shape; the native /
  -- sub-VM arms pull their bounds from `hnative` / `hcallee`.
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

end SVM.SBPF
