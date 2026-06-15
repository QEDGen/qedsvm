/-
  Layer 3b: 8 CU triple over the p-token Transfer magic-byte cascade (bytes 0xba0-0xbd8).
  3 jne-NT + 1 jeq-TAKEN under the 4 magic-match hypotheses; input-buffer bytes preserved.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenValidationPrelude

open SVM.SBPF
open Memory

/-- Default final-jeq target (PC 7 + 1 + 0xf61); base-parameterized variant takes it externally. -/
def transferArmTarget : Nat := 0xf69

def validationPreludeCr (base : Nat) (target : Nat) : CodeReq :=
  cr![ base + 0 ↦ .ldx .dword .r2 .r1 0x58,
       base + 1 ↦ .jne .r2 (.imm 0xa5) (base + 8),
       base + 2 ↦ .ldx .byte .r2 .r1 0x2910,
       base + 3 ↦ .jne .r2 (.imm 0xff) (base + 8),
       base + 4 ↦ .ldx .dword .r2 .r1 0x2960,
       base + 5 ↦ .jne .r2 (.imm 0xa5) (base + 8),
       base + 6 ↦ .ldx .byte .r2 .r1 0x5218,
       base + 7 ↦ .jeq .r2 (.imm 0xff) target ]

theorem p_token_transfer_validation_prelude_spec
    (base : Nat) (target : Nat)
    (initR1 initR2 : Nat)
    (m1 m3 : Nat) (m2 m4 : Nat)
    (hm1_lt : m1 < 2 ^ 64) (hm3_lt : m3 < 2 ^ 64)
    (hm1 : m1 = toU64 0xa5)
    (hm2 : m2 % 256 = toU64 0xff)
    (hm3 : m3 = toU64 0xa5)
    (hm4 : m4 % 256 = toU64 0xff) :
    cuTripleWithinMem 8 0 base target (validationPreludeCr base target)
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ m4 % 256) **
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4))
      (fun rt =>
        ((rt.containsRange (effectiveAddr initR1 0x58) 8 = true ∧
          rt.containsRange (effectiveAddr initR1 0x2910) 1 = true) ∧
          rt.containsRange (effectiveAddr initR1 0x2960) 8 = true) ∧
          rt.containsRange (effectiveAddr initR1 0x5218) 1 = true) := by
  have h0 := ldxdw_spec .r2 .r1 0x58 initR2 initR1 m1 (base + 0) (by decide) hm1_lt
  have h1 := jne_imm_spec .r2 0xa5 m1 (base + 1) (base + 8)
  have h2 := ldxb_spec  .r2 .r1 0x2910 m1 initR1 m2 (base + 2) (by decide)
  have h3 := jne_imm_spec .r2 0xff (m2 % 256) (base + 3) (base + 8)
  have h4 := ldxdw_spec .r2 .r1 0x2960 (m2 % 256) initR1 m3 (base + 4) (by decide) hm3_lt
  have h5 := jne_imm_spec .r2 0xa5 m3 (base + 5) (base + 8)
  have h6 := ldxb_spec  .r2 .r1 0x5218 m3 initR1 m4 (base + 6) (by decide)
  have h7 := jeq_imm_spec .r2 0xff (m4 % 256) (base + 7) target
  rw [show (if m1 ≠ toU64 0xa5 then (base + 8) else (base + 1) + 1) = base + 2 from by
        rw [hm1]; simp] at h1
  rw [show (if m2 % 256 ≠ toU64 0xff then (base + 8) else (base + 3) + 1) = base + 4 from by
        rw [hm2]; simp] at h3
  rw [show (if m3 ≠ toU64 0xa5 then (base + 8) else (base + 5) + 1) = base + 6 from by
        rw [hm3]; simp] at h5
  rw [show (if (m4 % 256) = toU64 0xff then target else (base + 7) + 1) = target
        from by rw [hm4]; simp] at h7
  unfold validationPreludeCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7]

end Examples.PTokenValidationPrelude
