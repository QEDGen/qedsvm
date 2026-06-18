/-
  Layer-3 GUARD (routing half) for the p-token balance check, harvested from
  H3dBalanceCheck.

  The proven AsmRefinesTokenTransfer arm only states the data transformation on
  the happy path (it REQUIRES `srcBalance ≥ txAmount`, assumed). This proves the
  ENFORCES direction's substantive half: on the VIOLATING branch
  (`srcBalance < txAmount`), the real bytecode does NOT continue to the effect —
  the `jlt` at `base+7` diverts execution to the error handler PC `h3dErrPc`.

  This is the same 8-insn window as `p_token_transfer_arm_h3d_spec`, with the
  branch flipped (`if_pos` instead of `if_neg`) and the exit set to the error PC
  instead of fall-through. Compose with the shared error-handler fault spec via
  `SVM.Solana.Patterns.enforcedFault_of_routes_then_handler` to obtain full
  `EnforcedFault` (next step: the handler CodeReq at `h3dErrPc`).
-/

import PToken.TransferArm.H3dBalanceCheck
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenTransferArmH3dBalanceGuard

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmH3dBalanceCheck

/-- Insufficient source balance routes the balance-check window to the error
    handler (`h3dErrPc`), not to the effect. The program enforces the balance
    check rather than silently performing the transfer. -/
theorem p_token_balance_insufficient_routes_to_error
    (base : Nat)
    (initR1 baseAddr srcState dstState txAmount srcBalance : Nat)
    (h_amt_lt : txAmount < 2 ^ 64)
    (h_bal_lt : srcBalance < 2 ^ 64)
    (h_src_ne2 : srcState % 256 ≠ 2)
    (h_dst_ne2 : dstState % 256 ≠ 2)
    (h_insufficient : srcBalance < txAmount) :
    cuTripleWithinMem 8 0 base h3dErrPc (h3dCr base)
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ baseAddr) **
        (.r3 ↦ᵣ srcState % 256) ** (.r5 ↦ᵣ dstState % 256) **
        (.r6 ↦ᵣ toU64 3) ** (.r7 ↦ᵣ toU64 0) **
        (effectiveAddr baseAddr 0x7a81 ↦U64 txAmount) **
        (effectiveAddr initR1 0xa0 ↦U64 srcBalance))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ txAmount) **
        (.r3 ↦ᵣ srcBalance) ** (.r5 ↦ᵣ dstState % 256) **
        (.r6 ↦ᵣ toU64 0) ** (.r7 ↦ᵣ toU64 1) **
        (effectiveAddr baseAddr 0x7a81 ↦U64 txAmount) **
        (effectiveAddr initR1 0xa0 ↦U64 srcBalance))
      (fun rt =>
        rt.containsRange (effectiveAddr baseAddr 0x7a81) 8 = true ∧
        rt.containsRange (effectiveAddr initR1 0xa0) 8 = true) := by
  have h0 := mov64_imm_spec .r6 0 (toU64 3) (base + 0) (by decide)
  have h1 := mov64_imm_spec .r7 0x11 (toU64 0) (base + 1) (by decide)
  have h2 := jeq_imm_spec .r3 2 (srcState % 256) (base + 2) h3dErrPc
  have h3 := jeq_imm_spec .r5 2 (dstState % 256) (base + 3) h3dErrPc
  have h4 := ldxdw_same_spec .r2 0x7a81 baseAddr txAmount (base + 4) (by decide) h_amt_lt
  have h5 := mov64_imm_spec .r7 1 (toU64 0x11) (base + 5) (by decide)
  have h6 := ldxdw_spec .r3 .r1 0xa0 (srcState % 256) initR1 srcBalance (base + 6)
                        (by decide) h_bal_lt
  have h7 := jlt_reg_spec .r3 .r2 srcBalance txAmount (base + 7) h3dErrPc
  rw [show (if srcState % 256 = toU64 2 then h3dErrPc else (base + 2) + 1) = base + 3 from by
        have hno : ¬ (srcState % 256 = toU64 2) := by
          show ¬ (srcState % 256 = 2); omega
        rw [if_neg hno]] at h2
  rw [show (if dstState % 256 = toU64 2 then h3dErrPc else (base + 3) + 1) = base + 4 from by
        have hno : ¬ (dstState % 256 = toU64 2) := by
          show ¬ (dstState % 256 = 2); omega
        rw [if_neg hno]] at h3
  rw [show (if srcBalance < txAmount then h3dErrPc else (base + 7) + 1) = h3dErrPc from by
        rw [if_pos h_insufficient]] at h7
  unfold h3dCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7]

end Examples.PTokenTransferArmH3dBalanceGuard
