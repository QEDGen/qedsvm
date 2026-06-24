/-
  secp256k1 ECDSA public-key recovery. Calls `lean-bridge`, which uses
  paritytech's `libsecp256k1 = 0.7.2` — the exact crate agave's
  `SyscallSecp256k1Recover` uses. Matching it verbatim is load-bearing: it differs
  from Bitcoin Core's libsecp256k1 (e.g. paritytech rejects high-S signatures,
  Bitcoin Core accepts). No pure-Lean curve spec; that is downstream work.
  Wired to `.sol_secp256k1_recover` via `Secp256k1.exec`.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Secp256k1

/-- ECDSA recovery outcome, mirroring agave's `Secp256k1RecoverError` plus a
    success case (64-byte pubkey `x || y`, no `0x04` prefix). The error tags
    (1/2/3) are *load-bearing*: the syscall arm uses them as r0 return codes. -/
inductive RecoverResult where
  /-- The 64-byte recovered pubkey, no leading `0x04`. -/
  | success (pubkey : ByteArray)
  /-- `r0 := 1`. Unreachable via the syscall (hash is fixed at 32 bytes); ABI completeness. -/
  | invalidHash
  /-- `r0 := 2`. The `recovery_id` is `≥ 4`. -/
  | invalidRecoveryId
  /-- `r0 := 3`. Signature parse failed (e.g. high-S) or point not recoverable. -/
  | invalidSignature
  deriving DecidableEq, Inhabited

/-- Recover a 64-byte uncompressed secp256k1 pubkey (no `0x04` prefix, Solana wire
    format) from a 32-byte hash, 1-byte recovery_id (0..=3), and 64-byte compact
    signature (r || s). Failures map to the `invalid*` variants. Implemented in Rust
    (`lean_secp256k1_recover`); opaque to the kernel but reducible by `native_decide`. -/
@[extern "lean_secp256k1_recover"]
opaque recover (hash : @& ByteArray) (recoveryId : UInt8) (sig : @& ByteArray) : RecoverResult

/-! ## `sol_secp256k1_recover` syscall

ABI: r1 = `*const [u8; 32]` hash, r2 = recovery_id (≥4 rejected),
r3 = `*const [u8; 64]` sig (r || s), r4 = `*mut [u8; 64]` out.
r0 = 0/1/2/3 (success / invalid hash / invalid recovery id / invalid sig). -/

def cu : Nat := 25_000

@[simp] def exec (s : State) : State :=
  let recId  := s.regs.r2
  let outA   := s.regs.r4
  -- H6: guard the hash `[r1,32)`, signature `[r3,64)` and output `[r4,64)` before
  -- recovery; only the `.success` arm writes the recovered pubkey.
  s.guardRead s.regs.r1 32 fun s =>
  s.guardRead s.regs.r3 64 fun s =>
  s.guardWrite outA 64 fun s =>
    let result : RecoverResult :=
      if recId > 3 then .invalidRecoveryId
      else recover (readBytes s.mem s.regs.r1 32) recId.toUInt8
                    (readBytes s.mem s.regs.r3 64)
    let errCode : Nat :=
      match result with
      | .success _         => 0
      | .invalidHash       => 1
      | .invalidRecoveryId => 2
      | .invalidSignature  => 3
    let mem' : Memory.Mem :=
      match result with
      | .success pubkey => writeBytes s.mem outA 64 pubkey
      | _               => s.mem
    { s with regs := s.regs.set .r0 errCode, mem := mem' }

/-- H6 fault direction: an out-of-region hash input `[r1,32)` (the first of the
    three guarded slices) traps with a typed access violation. -/
theorem exec_faults_oob (s : State)
    (hoob : s.regions.containsRange s.regs.r1 32 = false) :
    (exec s).vmError = some .accessViolation := by
  simp only [exec, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Companion to `exec_faults_oob`: the same OOB input also pins the
    `exitCode` sentinel (the `guardRead` fault sets both fields). The pair lets
    a `cuTripleFaultsWithin` corollary discharge its exitCode AND vmError
    conjuncts. -/
theorem exec_faults_oob_exitCode (s : State)
    (hoob : s.regions.containsRange s.regs.r1 32 = false) :
    (exec s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [exec, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

end Secp256k1
end SVM.SBPF
