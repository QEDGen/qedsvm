/-
  A vesting gate proved for every clock (#105).

  The program reads the clock, loads `unix_timestamp` and exits 0 at or after
  `cutoff`, 1 before it. `vestingGate_unlocks` and `vestingGate_locks` compose the
  environment-general clock getter with ordinary per-instruction triples, so they
  hold for any `env`, with `rt.sysvars = env` as one more `rr` clause.
-/

import SVM.SBPF.Macros
import SVM.SBPF.Runner

namespace Examples.VestingGate

open SVM.SBPF
open Memory

/-- ```
    0: mov64 r1, r10
    1: add64 r1, -40           ; a 40-byte frame buffer
    2: call sol_get_clock_sysvar
    3: ldxdw r2, [r1 + 32]     ; unix_timestamp
    4: jsge r2, cutoff, 7
    5: mov64 r0, 1
    6: exit
    7: mov64 r0, 0
    8: exit
    ``` -/
def vestingGate (cutoff : Int) : Array Insn :=
  #[ .mov64 .r1 (.reg .r10),
     .add64 .r1 (.imm (-40)),
     .call .sol_get_clock_sysvar,
     .ldx .dword .r2 .r1 32,
     .jsge .r2 (.imm cutoff) 7,
     .mov64 .r0 (.imm 1),
     .exit,
     .mov64 .r0 (.imm 0),
     .exit ]

/-! ## It runs as stated, under warped clocks -/

/-- The exit code at timestamp `ts`, under a run's own stack and region table. -/
def runGate (cutoff : Int) (ts : Nat) : Option Nat :=
  let env := { SysvarEnv.molluskDefaults with
    clock := { SysvarEnv.molluskDefaults.clock with unixTimestamp := ts } }
  (executeFn (Runner.fetchFromArray (vestingGate cutoff))
    (Runner.initialState { sysvars := env }) 20).exitCode

example : runGate 1000 999 = some 1 := by native_decide
example : runGate 1000 1000 = some 0 := by native_decide
example : runGate 1000 1001 = some 0 := by native_decide
-- `-5` as its u64 two's complement: before a positive cutoff, after a negative one.
example : runGate 1000 (2 ^ 64 - 5) = some 1 := by native_decide
example : runGate (-10) (2 ^ 64 - 5) = some 0 := by native_decide
example : runGate (-1) (2 ^ 64 - 5) = some 1 := by native_decide

/-! ## It's proved for every clock -/

/-- The instructions up to and including the branch. -/
abbrev prefixCode (cutoff : Int) : CodeReq :=
  (((((CodeReq.singleton 0 (.mov64 .r1 (.reg .r10))).union
    (CodeReq.singleton 1 (.add64 .r1 (.imm (-40))))).union
    (CodeReq.singleton 2 (.call .sol_get_clock_sysvar))).union
    (CodeReq.singleton 3 (.ldx .dword .r2 .r1 32))).union
    (CodeReq.singleton 4 (.jsge .r2 (.imm cutoff) 7)))

/-- At or after `cutoff`, the gate reaches its exit with `r0 = 0`. -/
theorem vestingGate_unlocks (env : SysvarEnv) (cutoff : Int)
    (fp out r0Old r1Old r2Old nCu : Nat) (old : ByteArray)
    (hOutEq : wrapAdd fp (toU64 (-40)) = out) (hOld : old.size = 40) (hAlign : out % 8 = 0)
    (hOut : out < Memory.INPUT_START) (hEff : effectiveAddr out 32 = out + 32)
    (hTs : env.clock.unixTimestamp < 2 ^ 64)
    (hGe : toSigned64 env.clock.unixTimestamp ≥ toSigned64 (toU64 cutoff))
    (hCu : ∀ s : State,
      (step (.call .sol_get_clock_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 6 nCu 0 8
      ((prefixCode cutoff).union (CodeReq.singleton 7 (.mov64 .r0 (.imm 0))))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1Old) ** (.r2 ↦ᵣ r2Old) ** (.r10 ↦ᵣ fp) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ toU64 0) ** (.r1 ↦ᵣ out) ** (.r2 ↦ᵣ env.clock.unixTimestamp) ** (.r10 ↦ᵣ fp) **
        ((out ↦Bytes env.clock.head) ** (effectiveAddr out 32 ↦U64 env.clock.unixTimestamp)))
      (fun rt => ((rt.sysvars = env ∧ rt.containsWritable out 40 = true) ∧
        rt.containsRange (effectiveAddr out 32) 8 = true)) := by
  have h0 := mov64_reg_spec .r1 .r10 r1Old fp 0 (by decide)
  have h1 := add64_imm_spec .r1 (-40) fp 1 (by decide)
  rw [hOutEq] at h1
  have h2 := call_sol_get_clock_sysvar_ts_spec env r0Old out 2 nCu old hOld hAlign hOut hEff hCu
  have h3 := ldxdw_spec .r2 .r1 32 r2Old out env.clock.unixTimestamp 3 (by decide) hTs
  have h4 := jsge_imm_taken_spec .r2 cutoff env.clock.unixTimestamp 4 7 hGe
  have h7 := mov64_imm_spec .r0 0 0 7 (by decide)
  sl_block_iter [h0, h1, h2, h3, h4, h7]

/-- Before `cutoff`, the gate reaches its other exit with `r0 = 1`. -/
theorem vestingGate_locks (env : SysvarEnv) (cutoff : Int)
    (fp out r0Old r1Old r2Old nCu : Nat) (old : ByteArray)
    (hOutEq : wrapAdd fp (toU64 (-40)) = out) (hOld : old.size = 40) (hAlign : out % 8 = 0)
    (hOut : out < Memory.INPUT_START) (hEff : effectiveAddr out 32 = out + 32)
    (hTs : env.clock.unixTimestamp < 2 ^ 64)
    (hLt : ¬ toSigned64 env.clock.unixTimestamp ≥ toSigned64 (toU64 cutoff))
    (hCu : ∀ s : State,
      (step (.call .sol_get_clock_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 6 nCu 0 6
      ((prefixCode cutoff).union (CodeReq.singleton 5 (.mov64 .r0 (.imm 1))))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1Old) ** (.r2 ↦ᵣ r2Old) ** (.r10 ↦ᵣ fp) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ toU64 1) ** (.r1 ↦ᵣ out) ** (.r2 ↦ᵣ env.clock.unixTimestamp) ** (.r10 ↦ᵣ fp) **
        ((out ↦Bytes env.clock.head) ** (effectiveAddr out 32 ↦U64 env.clock.unixTimestamp)))
      (fun rt => ((rt.sysvars = env ∧ rt.containsWritable out 40 = true) ∧
        rt.containsRange (effectiveAddr out 32) 8 = true)) := by
  have h0 := mov64_reg_spec .r1 .r10 r1Old fp 0 (by decide)
  have h1 := add64_imm_spec .r1 (-40) fp 1 (by decide)
  rw [hOutEq] at h1
  have h2 := call_sol_get_clock_sysvar_ts_spec env r0Old out 2 nCu old hOld hAlign hOut hEff hCu
  have h3 := ldxdw_spec .r2 .r1 32 r2Old out env.clock.unixTimestamp 3 (by decide) hTs
  have h4 := jsge_imm_not_taken_spec .r2 cutoff env.clock.unixTimestamp 4 7 hLt
  have h5 := mov64_imm_spec .r0 1 0 5 (by decide)
  sl_block_iter [h0, h1, h2, h3, h4, h5]

end Examples.VestingGate
