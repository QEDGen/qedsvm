/-
  Loader-serialized input layout (#40 gap 3) — the offset algebra tying the
  input region base (`r1` at entry, MM_INPUT_START) to per-account codec
  bases, so "account k, field f" claims don't re-derive byte offsets in
  every program proof.

  Aligned `bpf_loader` serialization (agave `serialize_parameters_aligned`):
  a u64 account count, then per NON-DUP account

      1   dup marker (0xff)
      1   is_signer
      1   is_writable
      1   is_executable
      4   original_data_len
      32  key
      32  owner
      8   lamports
      8   data_len            (= 88 header bytes)
      …   data (dataLen bytes)
      …   MAX_PERMITTED_DATA_INCREASE (10240) + pad to 8 (BPF u128 align)
      8   rent_epoch

  then the u64 instruction-data length, the instruction data, and the 32-byte
  program id. The formulas below are VALIDATED against offsets that the
  diff-tested p_token lifts anchor on real agave/mollusk executions
  (`p_token_transfer_input_layout`).
-/

import SVM.Solana.Abstract.Refinement

namespace SVM.Solana

open SVM.SBPF SVM.Solana.Abstract

/-- The input region opens with a u64 account count. -/
def ACCTS_COUNT_SIZE : Nat := 8

/-- Fixed per-account serialized header (dup/signer/writable/exec +
    original_data_len + key + owner + lamports + data_len). -/
def ACCT_HEADER_SIZE : Nat := 88

/-- agave's `MAX_PERMITTED_DATA_INCREASE`: realloc headroom serialized after
    every account's data. -/
def MAX_PERMITTED_DATA_INCREASE : Nat := 10240

/-- Round `n` up to a multiple of `a`. -/
def alignUp (n a : Nat) : Nat := (n + a - 1) / a * a

/-- Header-relative offsets of the fixed account fields. -/
def ACCT_KEY_OFF : Nat := 8
def ACCT_OWNER_OFF : Nat := 40
def ACCT_LAMPORTS_OFF : Nat := 72
def ACCT_DATA_LEN_OFF : Nat := 80

/-- One non-dup account's serialized footprint: header + data + realloc
    headroom padded to the BPF u128 alignment (8) + rent_epoch. -/
def acctSlotSize (dataLen : Nat) : Nat :=
  ACCT_HEADER_SIZE + alignUp (dataLen + MAX_PERMITTED_DATA_INCREASE) 8 + 8

/-- Offset of account k's slot (its dup-marker byte): the count word plus
    every preceding account's slot. -/
def acctSlotOff (dataLens : List Nat) (k : Nat) : Nat :=
  ACCTS_COUNT_SIZE + ((dataLens.take k).map acctSlotSize).foldr (· + ·) 0

/-- Offset of account k's DATA region — the per-account codec base. -/
def acctDataOff (dataLens : List Nat) (k : Nat) : Nat :=
  acctSlotOff dataLens k + ACCT_HEADER_SIZE

/-- Offset of the u64 instruction-data length (after the last account). -/
def instrLenOff (dataLens : List Nat) : Nat :=
  acctSlotOff dataLens dataLens.length

/-- Offset of the instruction data itself. -/
def instrDataOff (dataLens : List Nat) : Nat :=
  instrLenOff dataLens + 8

/-- Offset of the 32-byte program id (after the instruction data). -/
def programIdOff (dataLens : List Nat) (instrLen : Nat) : Nat :=
  instrDataOff dataLens + instrLen

/-- Absolute address of `fieldOff` inside account k's data, from the input
    region base (`r1` at entry). -/
def acctFieldAddr (inputBase : Nat) (dataLens : List Nat)
    (k fieldOff : Nat) : Nat :=
  inputBase + acctDataOff dataLens k + fieldOff

/-- State a transition's tracked accounts by input position: entry
    `(k, pre, post)` places account k's codec at its serialized data
    offset. Feeds `AsmRefinesTransitionPath`/`AsmRefinesFieldUpdates`
    without per-proof offset derivations. -/
def inputAccounts (inputBase : Nat) (dataLens : List Nat)
    (updates : List (Nat × List (Nat × FieldVal) × List (Nat × FieldVal))) :
    List AccountFields :=
  updates.map fun (k, pre, post) =>
    (inputBase + acctDataOff dataLens k, pre, post)

@[simp] theorem inputAccounts_nil (inputBase : Nat) (dataLens : List Nat) :
    inputAccounts inputBase dataLens [] = [] := rfl

@[simp] theorem inputAccounts_cons (inputBase : Nat) (dataLens : List Nat)
    (k : Nat) (pre post : List (Nat × FieldVal))
    (rest : List (Nat × List (Nat × FieldVal) × List (Nat × FieldVal))) :
    inputAccounts inputBase dataLens ((k, pre, post) :: rest) =
      (inputBase + acctDataOff dataLens k, pre, post) ::
        inputAccounts inputBase dataLens rest := rfl

/-! ## Validation — the formulas reproduce diff-tested lift anchors

The p_token Transfer lift (traced on a real agave/mollusk execution with two
165-byte token accounts) anchors the src account at `baseAddr + 96`, the dst
at `baseAddr + 10600`, the instruction-data length at `baseAddr + 21016` and
the instruction data at `baseAddr + 21024` — exactly this algebra. -/

theorem p_token_transfer_input_layout :
    acctDataOff [165, 165] 0 = 96 ∧
    acctDataOff [165, 165] 1 = 10600 ∧
    instrLenOff [165, 165] = 21016 ∧
    instrDataOff [165, 165] = 21024 := by decide

/-- The guarded fixtures read the account-count u64 at offset 0 and account
    0's header bytes from offset 8. -/
example : acctSlotOff [16] 0 = ACCTS_COUNT_SIZE := by decide

end SVM.Solana
