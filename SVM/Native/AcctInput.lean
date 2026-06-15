-- Account input view for native program handlers.
--
-- Trimmed-down per-account struct (`AcctInput`) that carries only the
-- fields a native program reads/writes, keeping Native modules decoupled
-- from Runner's BPF marshaling internals.

import SVM.SBPF.Memory

namespace SVM.Native

open SVM.SBPF.Memory

/-- Per-account info native handlers operate on. The `*RefAddr`/`*Ptr`
    fields are caller-memory addresses written through, mirroring agave's
    `BorrowedAccount` (mutations land in the caller's account view). -/
structure AcctInput where
  /-- Account pubkey (32 bytes, raw little-endian). -/
  key             : ByteArray
  /-- Current owner pubkey (32 bytes). System assign may update it. -/
  owner           : ByteArray
  /-- Lamport balance at parse time. -/
  lamports        : Nat
  /-- Account data length. -/
  dataLen         : Nat
  /-- Whether the BPF caller marked this account as a signer. -/
  isSigner        : Bool
  /-- Whether the BPF caller marked this account as writable. -/
  isWritable      : Bool
  /-- Caller-memory u64 slot holding the live lamport balance; System::Transfer writes here. -/
  lamportsRefAddr : Nat
  /-- Caller-memory pointer to the 32-byte owner slot. -/
  ownerPtr        : Nat
  /-- Caller-memory pointer to the account-data byte buffer. -/
  dataPtr         : Nat
  /-- Caller-memory u64 slot holding the live data length; resize ops (CreateAccount, Allocate) write it. -/
  dataLenRefAddr  : Nat
  deriving Inhabited

/-- Outcome of a native dispatch: `r0` CPI exit code, `cu` added to
    `State.cuConsumed` by the caller's CPI arm, `mem` post-call caller memory. -/
structure NativeResult where
  mem : Mem
  r0  : Nat
  cu  : Nat

end SVM.Native
