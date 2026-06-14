/-
  secp256k1 ECDSA public-key recovery.

  Calls directly into `qedsvm-rs/lean-bridge/` which uses paritytech's pure-Rust
  `libsecp256k1` crate (version 0.7.2) — the *exact* crate agave's
  `SyscallSecp256k1Recover` uses. The Rust side constructs the four-
  ctor `RecoverResult` inductive directly via Lean's runtime ABI; no
  intermediate C shim layer.

  Why match agave verbatim: paritytech's `libsecp256k1` has subtly
  different behavior from Bitcoin Core's `libsecp256k1` C library
  (e.g. high-S signatures: paritytech rejects via
  `Signature::parse_standard_slice`, Bitcoin Core accepts). For a
  reference interpreter, byte-for-byte conformance with mainnet is
  load-bearing.

  We deliberately do **not** ship a pure-Lean spec here. Verification of
  curve arithmetic is downstream work — its own project.

  Wired to `.sol_secp256k1_recover` via `Secp256k1.exec` below.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Secp256k1

/-- Outcome of ECDSA recovery. Mirrors agave's
    `solana_secp256k1_recover::Secp256k1RecoverError` plus a success
    case carrying the 64-byte recovered public key (`x || y`, no `0x04`
    prefix). The numeric tags (1, 2, 3 for the three errors) are
    *load-bearing*: the syscall arm uses them as Solana's syscall
    return codes. -/
inductive RecoverResult where
  /-- The 64-byte recovered pubkey, no leading `0x04`. -/
  | success (pubkey : ByteArray)
  /-- `r0 := 1`. Unreachable from the syscall arm in practice — the
      hash length is fixed at 32 bytes by the ABI. Included for ABI
      completeness. -/
  | invalidHash
  /-- `r0 := 2`. The `recovery_id` is `≥ 4`. -/
  | invalidRecoveryId
  /-- `r0 := 3`. Signature parse failed (e.g. high-S form rejected by
      `Signature::parse_standard_slice`), or recovery itself failed
      (point not recoverable). -/
  | invalidSignature
  deriving DecidableEq, Inhabited

/-- Recover a 64-byte uncompressed secp256k1 public key from a 32-byte
    message hash, a 1-byte recovery_id (0..=3), and a 64-byte compact
    ECDSA signature (r || s). Output omits the standard `0x04`
    uncompressed prefix — Solana's wire format.

    Failure path returns one of the three `invalid*` variants matching
    agave's `Secp256k1RecoverError` discriminants. Recovery_id > 3 ⇒
    `invalidRecoveryId`. Bad/high-S signature ⇒ `invalidSignature`.

    Implemented in Rust (`qedsvm-rs/lean-bridge/src/lib.rs::lean_secp256k1_recover`).
    Treated as opaque to the kernel: `decide` cannot reduce it, but
    `native_decide` will (via `ofReduceBool`). -/
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
  -- H6: agave translates the 32-byte hash (`[r1,32)`, Load), the 64-byte
  -- signature (`[r3,64)`, Load) and the 64-byte output (`[r4,64)`, Store)
  -- before the recovery — an out-of-region (or non-writable output) slice
  -- traps. Only the `.success` arm actually writes the recovered pubkey.
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

/-- H6 fault direction: an out-of-region 32-byte hash input `[r1,32)` traps
    with a typed access violation (the first of the three guarded slices —
    hash `[r1,32)`, signature `[r3,64)`, output `[r4,64)`). -/
theorem exec_faults_oob (s : State)
    (hoob : s.regions.containsRange s.regs.r1 32 = false) :
    (exec s).vmError = some .accessViolation := by
  simp only [exec, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

end Secp256k1
end SVM.SBPF
