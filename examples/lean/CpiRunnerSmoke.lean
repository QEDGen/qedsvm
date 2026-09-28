/-
  Smoke test for `Cpi.runner_cpiPath`: the generated zero-account caller path
  (`Sbpfv3CpiCallerLiftedSuccess_cpi_path`), instantiated with the runner's own
  callee relation (`runnerCallee registry .sol_invoke_signed`, restricted to
  the trivial invariant), reads as a statement about the runner
  `executeFnCpiWithFuel`: prefix, invoke, suffix to the exit, then the runner
  continues from the suffix end state. The callee's memory-preservation
  contract `hMem` stays a hypothesis.
-/

import SVM.SBPF.CpiRunner
import Generated.Sbpfv3CpiCallerLiftedSuccess

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Examples.CpiRunnerSmoke

open SVM.SBPF

open Memory in
theorem Sbpfv3CpiCaller_runner_path (registry : Nat → Option ByteArray)
    (baseAddr vR4Old vR7Old oldMemD_0 oldMemD_1 oldMemD_2 vR2Old oldMemD_3 oldMemD_4 oldMemD_5 oldMemD_6 vR3Old oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 oldMemD_14 vR6Old vR5Old : Nat)
    (holdMemD_6_lt : oldMemD_6 < 2 ^ 64)
    (holdMemD_8_lt : oldMemD_8 < 2 ^ 64)
    (holdMemD_10_lt : oldMemD_10 < 2 ^ 64)
    (holdMemD_12_lt : oldMemD_12 < 2 ^ 64)
    (cpiRdOld : ByteArray)
    (cpiR0Old : Nat)
    (cpi_oldMemD_0 : Nat)
    (hMem : ∀ s r, Cpi.restrict (Cpi.runnerCallee registry .sol_invoke_signed) (fun _ => True) s r →
      r.mem = s.mem) :
    Cpi.runnerCpiPath registry 34 0 0 34 3 0 41
      (((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r4 (.reg .r1))).union
        (CodeReq.singleton 1 (.lddw .r1 (12884901888)))).union
        (CodeReq.singleton 2 (.lddw .r7 (12884901984)))).union
        (CodeReq.singleton 3 (.stx .dword .r1 0 .r7))).union
        (CodeReq.singleton 4 (.lddw .r1 (12884901896)))).union
        (CodeReq.singleton 5 (.st .dword .r1 0 (0)))).union
        (CodeReq.singleton 6 (.lddw .r1 (12884901904)))).union
        (CodeReq.singleton 7 (.st .dword .r1 0 (0)))).union
        (CodeReq.singleton 8 (.lddw .r1 (12884901912)))).union
        (CodeReq.singleton 9 (.lddw .r2 (12884901976)))).union
        (CodeReq.singleton 10 (.stx .dword .r1 0 .r2))).union
        (CodeReq.singleton 11 (.lddw .r1 (12884901920)))).union
        (CodeReq.singleton 12 (.st .dword .r1 0 (8)))).union
        (CodeReq.singleton 13 (.lddw .r1 (12884901928)))).union
        (CodeReq.singleton 14 (.st .dword .r1 0 (8)))).union
        (CodeReq.singleton 15 (.lddw .r1 (12884901936)))).union
        (CodeReq.singleton 16 (.ldx .dword .r3 .r4 10352))).union
        (CodeReq.singleton 17 (.stx .dword .r1 0 .r3))).union
        (CodeReq.singleton 18 (.lddw .r1 (12884901944)))).union
        (CodeReq.singleton 19 (.ldx .dword .r3 .r4 10360))).union
        (CodeReq.singleton 20 (.stx .dword .r1 0 .r3))).union
        (CodeReq.singleton 21 (.lddw .r1 (12884901952)))).union
        (CodeReq.singleton 22 (.ldx .dword .r3 .r4 10368))).union
        (CodeReq.singleton 23 (.stx .dword .r1 0 .r3))).union
        (CodeReq.singleton 24 (.lddw .r1 (12884901960)))).union
        (CodeReq.singleton 25 (.ldx .dword .r3 .r4 10376))).union
        (CodeReq.singleton 26 (.stx .dword .r1 0 .r3))).union
        (CodeReq.singleton 27 (.lddw .r1 (578437695752307201)))).union
        (CodeReq.singleton 28 (.stx .dword .r2 0 .r1))).union
        (CodeReq.singleton 29 (.mov64 .r6 (.imm (0))))).union
        (CodeReq.singleton 30 (.lddw .r1 (12884901888)))).union
        (CodeReq.singleton 31 (.lddw .r2 (12884901984)))).union
        (CodeReq.singleton 32 (.mov64 .r3 (.imm (0))))).union
        (CodeReq.singleton 33 (.mov64 .r5 (.imm (0))))))
      ((((CodeReq.singleton 35 (.jeq .r0 (.imm (0)) 39)).union
        (CodeReq.singleton 39 (.st .dword .r7 0 (170)))).union
        (CodeReq.singleton 40 (.mov64 .r0 (.reg .r6)))))
      ((.r1 ↦ᵣ baseAddr) **
      (.r4 ↦ᵣ vR4Old) **
      (.r7 ↦ᵣ vR7Old) **
      (effectiveAddr (toU64 12884901888) 0 ↦U64 oldMemD_0) **
      (effectiveAddr (toU64 12884901896) 0 ↦U64 oldMemD_1) **
      (effectiveAddr (toU64 12884901904) 0 ↦U64 oldMemD_2) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr (toU64 12884901912) 0 ↦U64 oldMemD_3) **
      (effectiveAddr (toU64 12884901920) 0 ↦U64 oldMemD_4) **
      (effectiveAddr (toU64 12884901928) 0 ↦U64 oldMemD_5) **
      (effectiveAddr baseAddr 10352 ↦U64 oldMemD_6) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr (toU64 12884901936) 0 ↦U64 oldMemD_7) **
      (effectiveAddr baseAddr 10360 ↦U64 oldMemD_8) **
      (effectiveAddr (toU64 12884901944) 0 ↦U64 oldMemD_9) **
      (effectiveAddr baseAddr 10368 ↦U64 oldMemD_10) **
      (effectiveAddr (toU64 12884901952) 0 ↦U64 oldMemD_11) **
      (effectiveAddr baseAddr 10376 ↦U64 oldMemD_12) **
      (effectiveAddr (toU64 12884901960) 0 ↦U64 oldMemD_13) **
      (effectiveAddr (toU64 12884901976) 0 ↦U64 oldMemD_14) **
      (.r6 ↦ᵣ vR6Old) **
      (.r5 ↦ᵣ vR5Old) **
      (.r0 ↦ᵣ cpiR0Old) **
      (↦ReturnData cpiRdOld) **
      (effectiveAddr (toU64 12884901984) 0 ↦U64 cpi_oldMemD_0))
      (fun r => (.r0 ↦ᵣ (toU64 0)) **
      (.r7 ↦ᵣ (toU64 12884901984)) **
      (effectiveAddr (toU64 12884901984) 0 ↦U64 toU64 170 % 2 ^ (8 * 8)) **
      (.r6 ↦ᵣ (toU64 0)) **
      returnDataIs r.returnData **
      (.r1 ↦ᵣ toU64 12884901888) **
      (.r4 ↦ᵣ baseAddr) **
      (effectiveAddr (toU64 12884901888) 0 ↦U64 toU64 12884901984) **
      (effectiveAddr (toU64 12884901896) 0 ↦U64 toU64 0 % 2 ^ (8 * 8)) **
      (effectiveAddr (toU64 12884901904) 0 ↦U64 toU64 0 % 2 ^ (8 * 8)) **
      (.r2 ↦ᵣ toU64 12884901984) **
      (effectiveAddr (toU64 12884901912) 0 ↦U64 toU64 12884901976) **
      (effectiveAddr (toU64 12884901920) 0 ↦U64 toU64 8 % 2 ^ (8 * 8)) **
      (effectiveAddr (toU64 12884901928) 0 ↦U64 toU64 8 % 2 ^ (8 * 8)) **
      (effectiveAddr baseAddr 10352 ↦U64 oldMemD_6) **
      (.r3 ↦ᵣ toU64 0) **
      (effectiveAddr (toU64 12884901936) 0 ↦U64 oldMemD_6) **
      (effectiveAddr baseAddr 10360 ↦U64 oldMemD_8) **
      (effectiveAddr (toU64 12884901944) 0 ↦U64 oldMemD_8) **
      (effectiveAddr baseAddr 10368 ↦U64 oldMemD_10) **
      (effectiveAddr (toU64 12884901952) 0 ↦U64 oldMemD_10) **
      (effectiveAddr baseAddr 10376 ↦U64 oldMemD_12) **
      (effectiveAddr (toU64 12884901960) 0 ↦U64 oldMemD_12) **
      (effectiveAddr (toU64 12884901976) 0 ↦U64 toU64 578437695752307201) **
      (.r5 ↦ᵣ toU64 0))
      (fun rt => ((((((((((((((rt.containsWritable (effectiveAddr (toU64 12884901888) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901896) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901904) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901912) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901920) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901928) 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10352) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901936) 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10360) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901944) 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10368) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901952) 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10376) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901960) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901976) 0) 8 = true)
      (fun rt => rt.containsWritable (effectiveAddr (toU64 12884901984) 0) 8 = true)
      .sol_invoke_signed (fun _ => True) (fun r => (r.code = toU64 0)) :=
  Cpi.runner_cpiPath registry (Or.inl rfl)
    (Examples.Lifted.Sbpfv3CpiCallerLiftedSuccess.Sbpfv3CpiCallerLiftedSuccess_cpi_path
      baseAddr vR4Old vR7Old oldMemD_0 oldMemD_1 oldMemD_2 vR2Old oldMemD_3 oldMemD_4 oldMemD_5
      oldMemD_6 vR3Old oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13
      oldMemD_14 vR6Old vR5Old holdMemD_6_lt holdMemD_8_lt holdMemD_10_lt holdMemD_12_lt
      cpiRdOld cpiR0Old cpi_oldMemD_0 _ hMem)

end Examples.CpiRunnerSmoke
