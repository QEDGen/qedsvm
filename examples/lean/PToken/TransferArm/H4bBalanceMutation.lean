/-
  Layer 3b artifact (happy-path chain, H4b): Hoare triple over the
  **balance mutation slice** at bytes 0xA300-0xA350 of
  `qedsvm-rs/tests/fixtures/p_token.so`. **This is the arm that
  actually moves tokens.**

  The 11 instructions:

  ```
  a300: ldxb  r4, [r1 + 0x5219]     ← auth/signer byte
  a308: jeq   r4, 0x0, ...           ← NOT taken: auth ≠ 0
  a310: jeq   r2, 0x0, ...           ← NOT taken: amount ≠ 0
  a318: sub64 r3, r2                 ← src balance -= amount
  a320: stxdw [r1 + 0xa0], r3        ← STORE new src balance
  a328: ldxdw r3, [r1 + 0x29a8]      ← load dst balance
  a330: add64 r3, r2                 ← r3 += amount
  a338: stxdw [r1 + 0x29a8], r3      ← STORE new dst balance
  a340: mov64 r0, 0x0
  a348: ldxb  r3, [r1 + 0xcd]        ← close-flag byte
  a350: jne   r3, 0x1, -0x571        ← TAKEN: close ≠ 1; jumps to byte 0x77D0 (H5 exit)
  ```

  Chain context: entered via H4a's `jne r4, 0x163` (taken). At entry
  r2 holds the transfer amount (from H3d) and r3 holds the source
  balance (also from H3d), preserved through H3e/H3f/H4a since none
  touched r2 or r3.

  Spec: 11 CU advancing PC 0 → h4bTarget (synthetic local PC where
  the final jne lands; downstream glue maps to byte 0x77D0). Post:
  - src balance at `[r1+0xa0]` updated to `wrapSub srcBalance txAmount`
  - dst balance at `[r1+0x29a8]` updated to `wrapAdd dstBalance txAmount`
  - r0 := 0, r3 := closeFlag % 256, r4 := authByte % 256
  - r1, r2 preserved.

  3 if-collapses (2 jeq-imm-NT + 1 jne-imm-TAKEN). Under the
  no-underflow hypothesis already established by H3d's
  `srcBalance ≥ txAmount`, downstream consumers can reduce wrapSub
  to plain `Nat` subtraction (same pattern as `MinimalTransferAsm`).

  This is the slice that closes the gap to `BalanceSpec` —
  the actual token-balance shift the high-level spec aspires to.
-/

import PToken.TransferArm.H4aDestMintCheck
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH4bBalanceMutation

open SVM.SBPF
open Memory

def h4bTarget : Nat := 0x300
def h4bErrPc : Nat := 0x600

def h4bCr (base : Nat) (target : Nat) : CodeReq :=
  cr![ base + 0  ↦ .ldx .byte .r4 .r1 0x5219,
       base + 1  ↦ .jeq .r4 (.imm 0) h4bErrPc,
       base + 2  ↦ .jeq .r2 (.imm 0) h4bErrPc,
       base + 3  ↦ .sub64 .r3 (.reg .r2),
       base + 4  ↦ .stx .dword .r1 0xa0 .r3,
       base + 5  ↦ .ldx .dword .r3 .r1 0x29a8,
       base + 6  ↦ .add64 .r3 (.reg .r2),
       base + 7  ↦ .stx .dword .r1 0x29a8 .r3,
       base + 8  ↦ .mov64 .r0 (.imm 0),
       base + 9  ↦ .ldx .byte .r3 .r1 0xcd,
       base + 10 ↦ .jne .r3 (.imm 1) target ]

theorem p_token_transfer_arm_h4b_spec
    (base : Nat) (target : Nat)
    (initR0 initR1 initR4 txAmount srcBalance dstBalance : Nat)
    (authByte closeFlag : Nat)
    (h_dst_lt : dstBalance < 2 ^ 64)
    (h_amt_ne_0   : txAmount ≠ toU64 0)
    (h_auth_ne_0  : authByte % 256 ≠ toU64 0)
    (h_close_ne_1 : closeFlag % 256 ≠ toU64 1) :
    cuTripleWithinMem 11 0 base target (h4bCr base target)
      ((.r0 ↦ᵣ initR0) ** (.r1 ↦ᵣ initR1) **
        (.r2 ↦ᵣ txAmount) ** (.r3 ↦ᵣ srcBalance) ** (.r4 ↦ᵣ initR4) **
        (effectiveAddr initR1 0x5219 ↦ₘ authByte) **
        (effectiveAddr initR1 0xa0   ↦U64 srcBalance) **
        (effectiveAddr initR1 0x29a8 ↦U64 dstBalance) **
        (effectiveAddr initR1 0xcd   ↦ₘ closeFlag))
      ((.r0 ↦ᵣ toU64 0) ** (.r1 ↦ᵣ initR1) **
        (.r2 ↦ᵣ txAmount) ** (.r3 ↦ᵣ closeFlag % 256) **
        (.r4 ↦ᵣ authByte % 256) **
        (effectiveAddr initR1 0x5219 ↦ₘ authByte) **
        (effectiveAddr initR1 0xa0   ↦U64 wrapSub srcBalance txAmount) **
        (effectiveAddr initR1 0x29a8 ↦U64 wrapAdd dstBalance txAmount) **
        (effectiveAddr initR1 0xcd   ↦ₘ closeFlag))
      (fun rt =>
        (((rt.containsRange (effectiveAddr initR1 0x5219) 1 = true ∧
            rt.containsWritable (effectiveAddr initR1 0xa0) 8 = true) ∧
            rt.containsRange (effectiveAddr initR1 0x29a8) 8 = true) ∧
            rt.containsWritable (effectiveAddr initR1 0x29a8) 8 = true) ∧
            rt.containsRange (effectiveAddr initR1 0xcd) 1 = true) := by
  have h0  := ldxb_spec  .r4 .r1 0x5219 initR4 initR1 authByte (base + 0) (by decide)
  have h1  := jeq_imm_spec .r4 0 (authByte % 256) (base + 1) h4bErrPc
  have h2  := jeq_imm_spec .r2 0 txAmount (base + 2) h4bErrPc
  have h3  := sub64_reg_spec .r3 .r2 srcBalance txAmount (base + 3) (by decide)
  have h4  := stxdw_spec .r1 .r3 0xa0 initR1
                (wrapSub srcBalance txAmount) srcBalance (base + 4)
  have h5  := ldxdw_spec .r3 .r1 0x29a8 (wrapSub srcBalance txAmount)
                initR1 dstBalance (base + 5) (by decide) h_dst_lt
  have h6  := add64_reg_spec .r3 .r2 dstBalance txAmount (base + 6) (by decide)
  have h7  := stxdw_spec .r1 .r3 0x29a8 initR1
                (wrapAdd dstBalance txAmount) dstBalance (base + 7)
  have h8  := mov64_imm_spec .r0 0 initR0 (base + 8) (by decide)
  have h9  := ldxb_spec .r3 .r1 0xcd (wrapAdd dstBalance txAmount)
                initR1 closeFlag (base + 9) (by decide)
  have h10 := jne_imm_spec .r3 1 (closeFlag % 256) (base + 10) target
  -- Collapse the 2 NT jeqs.
  rw [show (if (authByte % 256) = toU64 0 then h4bErrPc else (base + 1) + 1) = base + 2 from by
        rw [if_neg h_auth_ne_0]] at h1
  rw [show (if txAmount = toU64 0 then h4bErrPc else (base + 2) + 1) = base + 3 from by
        rw [if_neg h_amt_ne_0]] at h2
  -- Collapse the TAKEN final jne.
  rw [show (if (closeFlag % 256) ≠ toU64 1 then target else (base + 10) + 1) = target from by
        rw [if_pos h_close_ne_1]] at h10
  unfold h4bCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end Examples.PTokenTransferArmH4bBalanceMutation
