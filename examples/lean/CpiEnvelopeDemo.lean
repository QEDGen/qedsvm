/-
  Per-call-site CPI envelope theorem, end-to-end on real bytecode (#40 gap 4).

  `cpi_envelope_caller.so` hand-builds a Rust-ABI `StableInstruction` on the
  program heap and invokes it. The walk terminates AT the invoke (proof-side
  CPI is the fail-closed `Cpi.exec` stub), so the lifted prefix's post owns
  exactly the envelope cells; this file reshapes them into
  `SVM.Solana.cpiEnvelope` — the trace-level invoke EVENT, stated against
  the binary:

  at the call site, the program hands `sol_invoke_signed`
      programId = the 32 bytes read from its instruction data
                  (`instrDataOff [0]` = 10352 — the gap-3 offset algebra),
      accounts  = [],
      data      = [1, 2, 3, 4, 5, 6, 7, 8].

  Composed with `cpiEnvelope_reads`, the runner's decode of this call is
  pinned by the caller's memory — no axiom about the call site remains.
-/

import Lean
import SVM.Solana.CpiEnvelope
import SVM.SBPF.Tactic.SL
import Generated.CpiEnvelopeCallerLifted

set_option maxRecDepth 65536

namespace Examples.CpiEnvelopeDemo

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Solana
open Examples.Lifted.CpiEnvelopeCaller

set_option maxHeartbeats 1600000 in
/-- The envelope event at the invoke call site, from the lifted prefix. -/
theorem cpi_envelope_at_call_site
    (baseAddr vR4Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 oldMemD_3 oldMemD_4 oldMemD_5 oldMemD_6 vR3Old oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 oldMemD_14 vR5Old : Nat)
    (holdMemD_6_lt : oldMemD_6 < 2 ^ 64)
    (holdMemD_8_lt : oldMemD_8 < 2 ^ 64)
    (holdMemD_10_lt : oldMemD_10 < 2 ^ 64)
    (holdMemD_12_lt : oldMemD_12 < 2 ^ 64)
    : cuTripleWithinMem 33 0 0 33
      ((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r4 (.reg .r1))).union
        (CodeReq.singleton 1 (.lddw .r1 (12884901888)))).union
        (CodeReq.singleton 2 (.lddw .r2 (12884901984)))).union
        (CodeReq.singleton 3 (.stx .dword .r1 0 .r2))).union
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
        (CodeReq.singleton 29 (.lddw .r1 (12884901888)))).union
        (CodeReq.singleton 30 (.lddw .r2 (12884901984)))).union
        (CodeReq.singleton 31 (.mov64 .r3 (.imm (0))))).union
        (CodeReq.singleton 32 (.mov64 .r5 (.imm (0))))))
      ((.r1 ↦ᵣ baseAddr) **
      (.r4 ↦ᵣ vR4Old) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr (toU64 12884901888) 0 ↦U64 oldMemD_0) **
      (effectiveAddr (toU64 12884901896) 0 ↦U64 oldMemD_1) **
      (effectiveAddr (toU64 12884901904) 0 ↦U64 oldMemD_2) **
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
      (.r5 ↦ᵣ vR5Old))
      (((.r1 ↦ᵣ toU64 12884901888) **
      (.r4 ↦ᵣ baseAddr) **
      (.r2 ↦ᵣ toU64 12884901984)) **
      cpiEnvelope (toU64 12884901888) (toU64 12884901984)
        (toU64 0 % 2 ^ (8 * 8)) (toU64 12884901976) (toU64 8 % 2 ^ (8 * 8))
        { programId := ⟨oldMemD_6, oldMemD_8, oldMemD_10, oldMemD_12⟩,
          accounts := [],
          data := [1, 2, 3, 4, 5, 6, 7, 8] } **
      ((effectiveAddr baseAddr 10352 ↦U64 oldMemD_6) **
      (.r3 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 10360 ↦U64 oldMemD_8) **
      (effectiveAddr baseAddr 10368 ↦U64 oldMemD_10) **
      (effectiveAddr baseAddr 10376 ↦U64 oldMemD_12) **
      (.r5 ↦ᵣ toU64 0)))
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
                  rt.containsWritable (effectiveAddr (toU64 12884901976) 0) 8 = true) := by
  have h := CpiEnvelopeCaller_lifted_spec baseAddr vR4Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 oldMemD_3 oldMemD_4 oldMemD_5 oldMemD_6 vR3Old oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 oldMemD_14 vR5Old holdMemD_6_lt holdMemD_8_lt holdMemD_10_lt holdMemD_12_lt
  simp only [cpiEnvelope, metasSL_nil, pubkeyIs, sepConj_emp_right_eq,
             List.length_nil, List.length_cons, Nat.reduceAdd]
  rw [show dataBA [1, 2, 3, 4, 5, 6, 7, 8]
        = PartialState.u64LE (toU64 578437695752307201) from rfl,
      ← memU64Is_eq_bytes_eq]
  sl_exact h

/-! ## Axiom gate

`AxiomAudit` cannot import this module (the ExamplesCpi lib is deliberately
non-precompiled — see the lakefile note), so the standard-axiom assertion
lives here, mirroring `#assert_std_axioms`. -/

open Lean Elab Command in
elab "#assert_std_axioms_local " id:ident : command => do
  let cName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms cName
  let bad := axs.filter (fun a =>
    !([``propext, ``Classical.choice, ``Quot.sound].contains a))
  unless bad.isEmpty do
    throwError "AXIOM AUDIT FAILED: '{cName}' depends on non-standard \
                axioms: {bad.toList}"

#assert_std_axioms_local Examples.CpiEnvelopeDemo.cpi_envelope_at_call_site

end Examples.CpiEnvelopeDemo
