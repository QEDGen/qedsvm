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

end SVM.SBPF
