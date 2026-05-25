-- Account input view for native program handlers.
--
-- The CPI handler in `Runner.lean` parses each caller-supplied
-- `AccountInfo` via `parseAccountInfo` into a `Runner.ParsedAcct`.
-- For native dispatch we hand the per-account info to the handler
-- in a trimmed-down struct (`AcctInput`) that only carries fields
-- a native program reads/writes — keeping the Native modules
-- decoupled from the BPF marshaling internals in Runner.

import SVM.SBPF.Memory

namespace SVM.Native

open SVM.SBPF.Memory

/-- Per-account info that native handlers operate on. The
    `*RefAddr`/`*Ptr` fields are caller-memory addresses the
    handler writes through, mirroring agave's `BorrowedAccount`
    API where mutations land in the caller's view of the account. -/
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
  /-- Caller-memory u64 slot holding the live lamport balance.
      Writing here is how System::Transfer mutates lamports. -/
  lamportsRefAddr : Nat
  /-- Caller-memory pointer to the 32-byte owner slot. -/
  ownerPtr        : Nat
  /-- Caller-memory pointer to the account-data byte buffer. -/
  dataPtr         : Nat
  /-- Caller-memory u64 slot holding the live data length. System
      operations that resize an account (CreateAccount, Allocate)
      write the new length here. -/
  dataLenRefAddr  : Nat
  deriving Inhabited

/-- Outcome of a native dispatch. `r0` is the CPI exit code surfaced
    to the BPF caller; `cu` is added to `State.cuConsumed` by the
    caller's CPI arm. `mem` is the post-call caller memory
    (lamport/owner/data mutations applied). -/
structure NativeResult where
  mem : Mem
  r0  : Nat
  cu  : Nat

end SVM.Native
