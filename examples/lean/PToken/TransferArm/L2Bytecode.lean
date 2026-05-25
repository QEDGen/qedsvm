/-
  Layer 3b artifact #4 (N+3): **Glue triple** composing setup →
  call_local → FP-cmp callee → exit_pops. **Closes the call-frame
  composition unknown** (the `callStackIs` atom from Lift #3 had not
  been exercised in a real triple chain).

  This is the first artifact in the project that:

  - Threads `callStackIs` through a real cross-procedure composition.
  - Uses `call_local_spec` + `exit_pops_spec` against compiler-emitted
    bytecode (not just unit-test fixtures).
  - Composes a re-usable triple (`fp_cmp_gt_path_spec`) at a non-zero
    base PC — exercising the parameterized form added in this session.

  **PC layout (synthetic, not byte-derived).** The artifact uses
  logical PCs separating caller and callee bodies for clarity:

  - PCs 0..3: setup insns (matches `transferArmSetupCr`)
  - PC 4: `call_local 100` (jump to callee)
  - PC 5: caller's continuation (where `exit_pops` returns)
  - PCs 100..127: callee body (matches `fpCmpGtPathCr 100`, skipping
    PCs 116-120 which are unreachable on the A > B path)
  - PC 128: callee's `exit` insn

  Real pinocchio bytecode places the setup at byte 0x76e8 and the
  callee at byte 0x185F8; the absolute PCs are 3805 and 12603
  respectively. A downstream consumer that wants this glue at
  absolute PCs would re-instantiate `fp_cmp_gt_path_spec` with
  `base := 12603` and shift the setup/call/exit PCs accordingly —
  the parameterized `base` argument exists exactly to support that.

  **Composition surface.** Once this artifact lands, the bytes-to-spec
  bridge for any "setup → call → callee → exit" slice of pinocchio
  reduces to: re-state the existing triples with the right base PC
  and chain via `sl_block_iter`. The remaining work for the full
  Transfer happy path is repetitive, not novel.
-/

import PToken.TransferArm.L1Setup
import CompilerRtFpCmp
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArm

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmSetup (transferArmSetupCr stackSlotOff)
open Examples.CompilerRtFpCmp
  (fpCmpGtPathCr signClearMask infBitPattern lookupTableBase gtOffset)

/-- Synthetic base PC for the callee body in this artifact. Real
    pinocchio uses byte 0x185F8 → absolute PC 12603; here we choose
    100 for compactness. The `fp_cmp_gt_path_spec` theorem is
    parameterized over this base. -/
def calleeEntry : Nat := 100

/-- PC of the caller's instruction right after `call_local` — this is
    where `exit_pops` will return to. -/
def callerContPc : Nat := 5

/-- Combined CodeReq for the glue: setup ∪ call_local ∪ callee_body ∪ exit. -/
def transferArmCr : CodeReq :=
  (((transferArmSetupCr.union
      (CodeReq.singleton 4 (.call_local calleeEntry))).union
      (fpCmpGtPathCr calleeEntry)).union
      (CodeReq.singleton (calleeEntry + 28) .exit))

theorem p_token_transfer_arm_spec
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 : Nat)
    (initR7 initR8 initR9 initR10 : Nat)
    (oldStackVal cmpTableGt : Nat)
    (h_initR6_sign  : initR6 < 2 ^ 63)
    (h_initR6_notNaN : initR6 ≤ infBitPattern)
    (h_initR6_pos   : initR6 > 0)
    (hTable_lt      : cmpTableGt < 2 ^ 64) :
    cuTripleWithinMem 29 0 0 callerContPc transferArmCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r5 ↦ᵣ initR5) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      ((.r1 ↦ᵣ lookupTableBase + gtOffset) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 toU64 0) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ toU64 0) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ gtOffset) ** (.r0 ↦ᵣ cmpTableGt) ** (.r4 ↦ᵣ initR6) **
        (.r5 ↦ᵣ toU64 0 ||| initR6) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      (fun rt =>
        rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true ∧
        rt.containsRange
          (effectiveAddr (lookupTableBase + gtOffset) 0) 8 = true) := by
  -- Component triples.
  have h_setup := Examples.PTokenTransferArmSetup.p_token_transfer_arm_setup_spec
    initR1 initR2 initR6 initR10 oldStackVal
  have h_call := call_local_spec calleeEntry [] initR6 initR7 initR8 initR9
    initR10 4
  -- Callee body: A := r1's value after setup = initR6; B := r2's value
  -- after setup = toU64 0. Initial register values for callee are
  -- their values at callee-entry-time.
  have hB_sign : (toU64 0) < 2 ^ 63 := by unfold toU64; decide
  have hB_notNaN : (toU64 0) ≤ infBitPattern := by
    unfold toU64 infBitPattern; decide
  have h_callee := Examples.CompilerRtFpCmp.fp_cmp_gt_path_spec
    calleeEntry initR6 (toU64 0)
    initR0 initR3 initR4 initR5 initR6 cmpTableGt
    h_initR6_sign hB_sign h_initR6_notNaN hB_notNaN h_initR6_pos hTable_lt
  have h_exit := exit_pops_spec
    ⟨callerContPc, initR6, initR7, initR8, initR9, initR10⟩
    [] infBitPattern initR7 initR8 initR9 (initR10 + 0x1000)
    (calleeEntry + 28)
  unfold transferArmCr
  sl_block_iter [h_setup, h_call, h_callee, h_exit]

end Examples.PTokenTransferArm
