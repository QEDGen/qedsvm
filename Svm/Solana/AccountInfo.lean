-- SL predicate for the Rust `solana_program::AccountInfo` struct as
-- programs see it after deserialization.
--
-- Layout (default Rust, 64-bit BPF target — mirrors the doc comment on
-- `Svm.SBPF.Runner.parseAccountInfo`):
--
--   offset  size  field
--   0       8     keyPtr           (*const Pubkey)
--   8       8     lamportsRcPtr    (*Rc<RefCell<&mut u64>>)
--   16      8     dataRcPtr        (*Rc<RefCell<&mut [u8]>>)
--   24      8     ownerPtr         (*const Pubkey)
--   32      8     rentEpoch        (u64)
--   40      1     isSigner         (u8)
--   41      1     isWritable       (u8)
--   42      1     executable       (u8)
--   43..48        padding          (5 bytes — opaque)
--   ----   ----
--   total = 48 bytes
--
-- This is the Rust-struct view (post-deserialization). The SBF
-- serialized input-region per-account block (88 bytes per
-- `serialize_parameters_aligned`) is a separate predicate to be added
-- when pinocchio-style proofs need it — pinocchio reads the serialized
-- form directly without going through the full Rust deserializer.
--
-- The pointers reference further memory regions that hold the actual
-- key/owner/lamports/data bytes. A future `accountInfoChain` predicate
-- will compose `accountInfoHeader` with the indirected payloads;
-- today's first cut is the header alone.

import Svm.SBPF.SepLogic

namespace Svm.Solana

open Svm.SBPF

/-! ## AccountInfo header struct -/

/-- Load-bearing fields of the 48-byte Rust `AccountInfo` struct.
    Pointers are stored as `Nat` (VM addresses); boolean flags as
    `Nat` in {0, 1} matching the u8 byte representation. -/
structure AcctInfoHeader where
  keyPtr        : Nat
  lamportsRcPtr : Nat
  dataRcPtr     : Nat
  ownerPtr      : Nat
  rentEpoch     : Nat
  isSigner      : Nat
  isWritable    : Nat
  executable    : Nat
  deriving Inhabited

/-! ## Field offsets -/

def ACCT_INFO_KEY_PTR_OFF       : Nat := 0
def ACCT_INFO_LAMPORTS_PTR_OFF  : Nat := 8
def ACCT_INFO_DATA_PTR_OFF      : Nat := 16
def ACCT_INFO_OWNER_PTR_OFF     : Nat := 24
def ACCT_INFO_RENT_EPOCH_OFF    : Nat := 32
def ACCT_INFO_IS_SIGNER_OFF     : Nat := 40
def ACCT_INFO_IS_WRITABLE_OFF   : Nat := 41
def ACCT_INFO_EXECUTABLE_OFF    : Nat := 42

/-- Total serialized size of the Rust `AccountInfo` struct (including
    5 bytes of trailing padding). -/
def ACCT_INFO_SIZE : Nat := 48

/-- Size of the trailing opaque padding (`43..48`). -/
def ACCT_INFO_PAD_SIZE : Nat := 5

/-! ## SL predicate -/

/-- An `AccountInfo` struct at byte address `base` with the given
    pointer / flag fields. The 5-byte trailing padding (`base+43 ..
    base+48`) is carried as an opaque `pad : ByteArray` frame; the
    well-formed caller requires `pad.size = ACCT_INFO_PAD_SIZE`. -/
def accountInfoHeader (base : Nat) (h : AcctInfoHeader) (pad : ByteArray) :
    Assertion :=
  ((base + ACCT_INFO_KEY_PTR_OFF)      ↦U64 h.keyPtr)        **
  ((base + ACCT_INFO_LAMPORTS_PTR_OFF) ↦U64 h.lamportsRcPtr) **
  ((base + ACCT_INFO_DATA_PTR_OFF)     ↦U64 h.dataRcPtr)     **
  ((base + ACCT_INFO_OWNER_PTR_OFF)    ↦U64 h.ownerPtr)      **
  ((base + ACCT_INFO_RENT_EPOCH_OFF)   ↦U64 h.rentEpoch)     **
  ((base + ACCT_INFO_IS_SIGNER_OFF)    ↦ₘ   h.isSigner)      **
  ((base + ACCT_INFO_IS_WRITABLE_OFF)  ↦ₘ   h.isWritable)    **
  ((base + ACCT_INFO_EXECUTABLE_OFF)   ↦ₘ   h.executable)    **
  ((base + 43)                          ↦Bytes pad)

end Svm.Solana
