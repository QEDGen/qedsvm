/-
Axiom audit gate (soundness CI): `lake build Examples` fails if any flagship
theorem acquires an axiom outside {propext, Classical.choice, Quot.sound}.
On failure, either a proof regressed to sorry/native_decide, or a new axiom
legitimately belongs — add it to the per-theorem allow-list with justification.
-/
import Lean
import SVM.SBPF.Bounded
import SVM.SBPF.BoundedCpi
import SVM.SBPF.CodecRead
import SVM.Solana.InputLayout
import SVM.Solana.CpiEnvelope
import Generated.PTokenTransferTracedLifted
import PToken.TransferRefinement
import PToken.TransferArm.FullHappyPath
import Generated.VaultRefinement
import Generated.CounterRefinement
import Generated.AbortCallerLifted
import Generated.OobSecp256k1Lifted
import Generated.OobClockSysvarLifted
import Generated.OobRentSysvarLifted
import Generated.OobSetReturnDataLifted
import Generated.OobCreatePdaLifted
import Generated.OobSha256Lifted
import Generated.GuardedCounterTransition
import Generated.GuardedAbortTransition
import Generated.GuardedOobTransition

open Lean Elab Command

/-- The classical axioms every theorem is allowed to depend on. -/
private def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_std_axioms foo` fails elaboration unless `foo` depends only on the
    standard classical axioms. The soundness gate for flagship theorems. -/
elab "#assert_std_axioms " id:ident : command => do
  let cName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms cName
  let bad := axs.filter (fun a => !stdAxioms.contains a)
  unless bad.isEmpty do
    throwError "AXIOM AUDIT FAILED: '{cName}' depends on non-standard axioms: {bad.toList}"

#assert_std_axioms Examples.Lifted.PTokenTransfer.PTokenTransfer_lifted_spec
#assert_std_axioms Examples.Lifted.PTokenTransfer.PTokenTransfer_balance_correct
#assert_std_axioms Examples.PTokenTransferRefinement.refines_asm
-- #25: the token arms' obligation is the layout-general N-account
-- `AsmRefinesFieldUpdates`, with per-account accessor corollaries.
#assert_std_axioms SVM.Solana.Abstract.asmRefinesFieldUpdates_singleton
#assert_std_axioms Examples.PTokenTransferRefinement.ensures_src
#assert_std_axioms Examples.PTokenTransferRefinement.ensures_dst
#assert_std_axioms Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_spec
#assert_std_axioms Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_terminates
#assert_std_axioms Examples.VaultRefinement.refines_asm
#assert_std_axioms Examples.VaultRefinement.ensures
#assert_std_axioms Examples.CounterRefinement.refines_asm
#assert_std_axioms Examples.CounterRefinement.ensures

-- #40 gap 1: the MECHANICALLY-EMITTED whole-transition bundle (success +
-- abort paths of guarded_counter, each a post-carrying terminating triple
-- composed with the shared `.exit` via `cuTripleWithinMem_seq_exit`) must
-- stay axiom-clean — transitively covering the ExitTriple/Transition library
-- layer and both per-path trace-guided lifts.
#assert_std_axioms Examples.GuardedCounterTransition.guarded_counter_transition
-- The fault-path variant: the panic conjunct is an `AsmRefinesTransitionFault`
-- (typed .abort via `cuTripleWithinMem_seq_fault_pure`), mixed with the
-- success `AsmRefinesTransitionPath` in one bundle.
#assert_std_axioms Examples.GuardedAbortTransition.guarded_abort_transition
-- The OOB variant: the guard-fail conjunct is an `AsmRefinesTransitionFault
-- … .accessViolation` via the Mem-Mem `cuTripleWithinMem_seq_fault`
-- (combined rr = prefix ∧ OOB region condition).
#assert_std_axioms Examples.GuardedOobTransition.guarded_oob_transition
-- The C-ABI invoke terminal's typed-fault spec.
#assert_std_axioms SVM.SBPF.call_sol_invoke_signed_c_faults_spec
-- Gap 3: the loader-serialization offset algebra must reproduce the
-- diff-tested p_token lift anchors decide-only.
#assert_std_axioms SVM.Solana.p_token_transfer_input_layout
-- Gap 4: the CPI envelope encodings (Rust + C ABI) answer the runner's exact
-- decode reads from a holdsFor witness — axiom-clean via the #48 forward
-- bridges — and the pid_read bridges make the runner's program-id read
-- LITERALLY the encoded limbs (the runner's pid is read as four u64 limbs).
#assert_std_axioms SVM.Solana.cpiEnvelope_reads
#assert_std_axioms SVM.Solana.cpiEnvelopeC_reads
#assert_std_axioms SVM.Solana.cpiEnvelope_pid_read
#assert_std_axioms SVM.Solana.cpiEnvelopeC_pid_read
-- The per-call-site envelope event (`CpiEnvelopeDemo.cpi_envelope_at_call_site`)
-- carries its own in-module assertion: the ExamplesCpi lib is deliberately
-- non-precompiled (lakefile note), and importing it here would re-trigger the
-- poisoned-dylib path.

-- Phase 7 sub-item 3 (emitter half): the typed-fault corollary and its running
-- prefix must stay axiom-clean (no sorry/native_decide leaking into the
-- abort-path proof — the disjointness is `decide`, the prefix `sl_block_auto`).
#assert_std_axioms Examples.Lifted.AbortCaller.AbortCaller_lifted_spec
#assert_std_axioms Examples.Lifted.AbortCaller.AbortCaller_fault_correct

-- H6 OOB-fault library half (accessViolation family): the typed-fault syscall
-- triple + its composition shape must stay axiom-clean (the foundation the
-- OOB `*_fault_correct` emitter half will compose).
#assert_std_axioms SVM.SBPF.call_sol_secp256k1_recover_faults_oob_spec
#assert_std_axioms SVM.SBPF.mov_r1_then_secp_oob_fault_correct
#assert_std_axioms Examples.Lifted.OobSecp256k1.OobSecp256k1_lifted_spec
#assert_std_axioms Examples.Lifted.OobSecp256k1.OobSecp256k1_fault_correct
#assert_std_axioms SVM.SBPF.call_sol_get_clock_sysvar_faults_oob_spec
#assert_std_axioms Examples.Lifted.OobClockSysvar.OobClockSysvar_fault_correct
#assert_std_axioms SVM.SBPF.call_sol_get_rent_sysvar_faults_oob_spec
#assert_std_axioms Examples.Lifted.OobRentSysvar.OobRentSysvar_fault_correct
#assert_std_axioms SVM.SBPF.call_sol_set_return_data_faults_oob_spec
#assert_std_axioms Examples.Lifted.OobSetReturnData.OobSetReturnData_fault_correct
#assert_std_axioms SVM.SBPF.call_sol_create_program_address_faults_oob_spec
#assert_std_axioms Examples.Lifted.OobCreatePda.OobCreatePda_fault_correct
#assert_std_axioms SVM.SBPF.call_sol_sha256_faults_oob_spec
#assert_std_axioms Examples.Lifted.OobSha256.OobSha256_fault_correct

-- StateBounded invariant (audit L5 + L3): must remain decide-only, never sorry/native_decide.
-- step_bounded = per-insn preservation (incl. r10 discipline); executeFn_bounded = multi-step
-- closure; initialState_bounded = runner base case; mem_byte_canonical = L3 fence.
#assert_std_axioms SVM.SBPF.step_bounded
#assert_std_axioms SVM.SBPF.executeFn_bounded
#assert_std_axioms SVM.SBPF.initialState_bounded
#assert_std_axioms SVM.SBPF.mem_byte_canonical

-- Phase 7 sub-item 4 (Stages A+B): StateBounded on the RUNTIME path.
-- Stage A = CPI-free transfer (executeFnCpi coincides with executeFn);
-- Stage B = the genuine cross-CPI chain (CPI commit step → fresh sub-VM
-- state → fuel-induction wrapper → end-to-end Runner.run), HYPOTHESIS-FREE:
-- the once-staged black boxes are discharged by Native.dispatch_bounded
-- (all four native handler modules) and step_exitBounded (per-step exit-code
-- sweep over execSyscall_exitBounded).
#assert_std_axioms SVM.SBPF.executeFnCpi_bounded_of_no_cpi
#assert_std_axioms SVM.SBPF.run_bounded_of_no_cpi
#assert_std_axioms SVM.SBPF.cpiCallNextState_bounded
#assert_std_axioms SVM.SBPF.buildCalleeVM_bounded
#assert_std_axioms SVM.SBPF.execSyscall_exitBounded
#assert_std_axioms SVM.SBPF.step_exitBounded
#assert_std_axioms SVM.Native.dispatch_bounded
#assert_std_axioms SVM.SBPF.executeFnCpiWithFuel_bounded
#assert_std_axioms SVM.SBPF.run_bounded

-- Issue #48: holdsFor↔read bridges for codecCoarse field atoms. The qedgen
-- discharge-bridge glue (encodeState read-conjunction ↔ holdsFor codec). Forward
-- bridges are unconditional; reverse bridges are byte-canonicality-gated. All
-- must stay axiom-clean — they bottom out at omega/simp, never sorry.
#assert_std_axioms SVM.SBPF.readU8_of_holdsFor_memByteIs
#assert_std_axioms SVM.SBPF.readU64_of_holdsFor_memU64Is
#assert_std_axioms SVM.SBPF.pubkeyAt_of_holdsFor_pubkeyIs
#assert_std_axioms SVM.SBPF.holdsFor_memByteIs_of_read
#assert_std_axioms SVM.SBPF.holdsFor_memU64Is_of_read
#assert_std_axioms SVM.SBPF.holdsFor_memByteIs_of_read_bounded
#assert_std_axioms SVM.SBPF.holdsFor_memU64Is_of_read_bounded
#assert_std_axioms SVM.SBPF.holdsFor_codecCoarse_field

-- Issue #48 Option A: reverse codec reassembly (read-conjunction → holdsFor
-- codec) for scalar layouts. The "build the pre from encodeState" direction.
-- Transitively covers fieldCompat/fieldCoarse_on_bytes/codecState_*/the union +
-- range-disjoint helpers. Must stay axiom-clean (omega/simp, never sorry).
#assert_std_axioms SVM.SBPF.holdsFor_codecCoarse_of_reads
#assert_std_axioms SVM.SBPF.holdsFor_codecCoarse_of_reads_bounded
