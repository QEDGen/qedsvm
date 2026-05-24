/-
  Layer 3b deliverable: Hoare triple over the p-token Transfer
  **validation prelude** — the 8-instruction magic-byte cascade at
  bytes 0xba0-0xbd8 of `qedsvm-rs/tests/fixtures/p_token.so` (release
  `p-token@v1.0.0-rc.1`).

  This is the first end-to-end Hoare triple over compiler-emitted
  Solana bytecode in the project. Scope chosen deliberately small —
  retires the "branch composition at scale" unknown noted in
  `docs/p-token-spike.md` before scaling to the full Transfer path.

  The 8 instructions, lifted from `qedsvm-rs/tests/fixtures/p_token.disasm`:

  ```
  ba0: 79 12 58 00 ...      ldxdw r2, [r1 + 0x58]
  ba8: 55 02 06 00 a5 00 .. jne   r2, 0xa5, +0x6     ← validation 1
  bb0: 71 12 10 29 ...      ldxb  r2, [r1 + 0x2910]
  bb8: 55 02 04 00 ff 00 .. jne   r2, 0xff, +0x4     ← validation 2
  bc0: 79 12 60 29 ...      ldxdw r2, [r1 + 0x2960]
  bc8: 55 02 02 00 a5 00 .. jne   r2, 0xa5, +0x2     ← validation 3
  bd0: 71 12 18 52 ...      ldxb  r2, [r1 + 0x5218]
  bd8: 15 02 61 0f ff 00 .. jeq   r2, 0xff, +0xf61   ← validation 4 (taken on success)
  ```

  Semantics: pinocchio validates its own zero-copy input-buffer
  layout via 4 magic-byte checks at fixed offsets. The 3 `jne`s
  short-circuit to a fall-through error path; the final `jeq` jumps
  to the actual Transfer logic at PC offset +0xf61 (byte 0x76e8)
  *only when all 4 magic bytes match the expected pattern*. The
  happy path through the cascade is therefore a deterministic linear
  walk under the hypothesis "all 4 magic bytes match".

  Spec: given the 4 magic-match hypotheses in the precondition, the
  validation prelude executes in 8 CUs and lands at PC 0xf69 (the
  target of the final `jeq` in local PC numbering) with input-buffer
  bytes preserved.
-/

import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic
import Svm.SBPF.Macros

namespace Examples.PTokenValidationPrelude

open Svm.SBPF
open Memory

/-- Local PC numbering: PCs 0-7 cover the 8 instructions; PC 0xf69
    is the target of the final `jeq` (PC 7 + 1 + 0xf61). -/
def transferArmTarget : Nat := 0xf69

/-- The CodeReq for the 8-instruction validation prelude. Left-folded
    `singleton.union` chain matching the pattern in `Macros.lean`. -/
def validationPreludeCr : CodeReq :=
  (((((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0x58)).union
        (CodeReq.singleton 1 (.jne .r2 (.imm 0xa5) 8))).union
        (CodeReq.singleton 2 (.ldx .byte .r2 .r1 0x2910))).union
        (CodeReq.singleton 3 (.jne .r2 (.imm 0xff) 8))).union
        (CodeReq.singleton 4 (.ldx .dword .r2 .r1 0x2960))).union
        (CodeReq.singleton 5 (.jne .r2 (.imm 0xa5) 8))).union
        (CodeReq.singleton 6 (.ldx .byte .r2 .r1 0x5218))).union
        (CodeReq.singleton 7 (.jeq .r2 (.imm 0xff) transferArmTarget))

theorem p_token_transfer_validation_prelude_spec
    (initR1 initR2 : Nat)
    (m1 m3 : Nat) (m2 m4 : Nat)
    (hm1_lt : m1 < 2 ^ 64) (hm3_lt : m3 < 2 ^ 64)
    (hm1 : m1 = toU64 0xa5)
    (hm2 : m2 % 256 = toU64 0xff)
    (hm3 : m3 = toU64 0xa5)
    (hm4 : m4 % 256 = toU64 0xff) :
    cuTripleWithinMem 8 0 transferArmTarget validationPreludeCr
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
      -- Left-folded ∧ per sl_block_iter's docstring constraint:
      -- "rr_goal must be a left-folded ∧ of the memory steps' rr's in
      -- the same order they appear in the spec list."
      (fun rt =>
        ((rt.containsRange (effectiveAddr initR1 0x58) 8 = true ∧
          rt.containsRange (effectiveAddr initR1 0x2910) 1 = true) ∧
          rt.containsRange (effectiveAddr initR1 0x2960) 8 = true) ∧
          rt.containsRange (effectiveAddr initR1 0x5218) 1 = true) := by
  -- Each jne's exit PC is `if vDst ≠ toU64 imm then target else pc + 1`.
  -- Under the magic-match hypotheses, the `≠` reduces to False and the
  -- conditional resolves to `pc + 1`, yielding a deterministic linear walk.
  have h0 := ldxdw_spec .r2 .r1 0x58 initR2 initR1 m1 0 (by decide) hm1_lt
  have h1 := jne_imm_spec .r2 0xa5 m1 1 8
  have h2 := ldxb_spec  .r2 .r1 0x2910 m1 initR1 m2 2 (by decide)
  have h3 := jne_imm_spec .r2 0xff (m2 % 256) 3 8
  have h4 := ldxdw_spec .r2 .r1 0x2960 (m2 % 256) initR1 m3 4 (by decide) hm3_lt
  have h5 := jne_imm_spec .r2 0xa5 m3 5 8
  have h6 := ldxb_spec  .r2 .r1 0x5218 m3 initR1 m4 6 (by decide)
  have h7 := jeq_imm_spec .r2 0xff (m4 % 256) 7 transferArmTarget
  -- Reduce each conditional exit PC to its non-branching form using
  -- the magic-match hypotheses. Each jne stays at pc+1 (not taken);
  -- the final jeq fires (taken) and goes to transferArmTarget.
  rw [show (if m1 ≠ toU64 0xa5 then (8 : Nat) else 1 + 1) = 2 from by
        rw [hm1]; simp] at h1
  rw [show (if m2 % 256 ≠ toU64 0xff then (8 : Nat) else 3 + 1) = 4 from by
        rw [hm2]; simp] at h3
  rw [show (if m3 ≠ toU64 0xa5 then (8 : Nat) else 5 + 1) = 6 from by
        rw [hm3]; simp] at h5
  -- jeq's exit PC uses `=` (jump if equal), unlike jne's `≠`.
  rw [show (if (m4 % 256) = toU64 0xff then transferArmTarget else 7 + 1) = transferArmTarget
        from by rw [hm4]; simp] at h7
  -- All 8 specs now have concrete exit PCs forming a linear chain
  -- 0 → 2 → 4 → 6 → 8 → transferArmTarget (wait, this doesn't quite
  -- work — jne advances by 2 since it stays at pc+1 = 2 after PC 1).
  -- Actually: 0 → 1 (ldxdw advances PC by 1), 1 → 2 (jne not taken),
  -- 2 → 3, 3 → 4, 4 → 5, 5 → 6, 6 → 7, 7 → transferArmTarget.
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7]

end Examples.PTokenValidationPrelude
