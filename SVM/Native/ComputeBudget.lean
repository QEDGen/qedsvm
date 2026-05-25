-- The Solana ComputeBudget program — native, not BPF.
--
-- agave's `solana_compute_budget_program::Entrypoint` is a single
-- `declare_process_instruction!(Entrypoint, 150, |_| Ok(()))` —
-- charge 150 CU, return success, no state mutation. The real
-- semantics live at the transaction level (the runtime inspects the
-- ComputeBudget instructions on a *transaction* before scheduling
-- and uses them to size the CU budget / loaded-accounts-data
-- limit). CPI into ComputeBudget is therefore a no-op from the
-- callee's perspective.
--
-- qedsvm models per-instruction, not per-transaction, so the
-- runtime-level behavior is out of scope (Tier 4 in the
-- production-parity roadmap). What we DO model here is the CPI
-- path: a BPF program that calls `invoke(&compute_budget_ix, ...)`
-- sees `r0 = 0` and 150 CU charged, matching agave.

import SVM.Native.AcctInput

namespace SVM.Native.ComputeBudget

open SVM.SBPF.Memory
open SVM.Native

/-- ComputeBudget program-id (`ComputeBudget111111111111111111111111111111`)
    encoded little-endian as a `Nat`. The bytes are
    `[3, 6, 70, 111, 229, 33, 23, 50, 255, 236, 173, 186, 114, 195,
    155, 231, 188, 140, 229, 187, 197, 247, 18, 107, 44, 67, 155,
    58, 64, 0, 0, 0]` (the result of base58-decoding the canonical
    pubkey string). -/
def PROGRAM_ID : Nat :=
  0x000000403a9b432c6b12f7c5bbe58cbce79bc372baadecff321721e56f460603

/-- `DEFAULT_COMPUTE_UNITS` from
    `solana-compute-budget-program/src/lib.rs`. Same for every
    ComputeBudget variant — the entrypoint is just a constant. -/
def CU_DEFAULT : Nat := 150

/-! ## ComputeBudgetInstruction enum

Mirrors agave's `solana_compute_budget_interface::ComputeBudgetInstruction`.
Decoded for spec fidelity; `dispatch` treats every variant the same
way (no-op + 150 CU), matching agave's CPI behavior. -/

inductive ComputeBudgetIx
  /-- Deprecated `RequestUnits { units, additional_fee }`.
      Discriminant 0. Agave rejects this at the transaction level. -/
  | requestUnits (units additionalFee : Nat)
  /-- `RequestHeapFrame(bytes)`. Discriminant 1. -/
  | requestHeapFrame (bytes : Nat)
  /-- `SetComputeUnitLimit(units)`. Discriminant 2. -/
  | setComputeUnitLimit (units : Nat)
  /-- `SetComputeUnitPrice(microlamports)`. Discriminant 3. -/
  | setComputeUnitPrice (microlamports : Nat)
  /-- `SetLoadedAccountsDataSizeLimit(bytes)`. Discriminant 4. -/
  | setLoadedAccountsDataSizeLimit (bytes : Nat)
  /-- Unknown variant (forward-compat). -/
  | unknown (discriminant : Nat)
  deriving Inhabited

/-- Read a u32 LE at offset `off`. Returns 0 past the end. -/
private def readU32LE (bs : ByteArray) (off : Nat) : Nat :=
  if off + 4 > bs.size then 0
  else
    (bs.get! off).toNat +
    (bs.get! (off + 1)).toNat * 0x100 +
    (bs.get! (off + 2)).toNat * 0x10000 +
    (bs.get! (off + 3)).toNat * 0x1000000

/-- Read a u64 LE at offset `off`. Returns 0 past the end. -/
private def readU64LE (bs : ByteArray) (off : Nat) : Nat :=
  if off + 8 > bs.size then 0
  else
    (bs.get! off).toNat +
    (bs.get! (off + 1)).toNat * 0x100 +
    (bs.get! (off + 2)).toNat * 0x10000 +
    (bs.get! (off + 3)).toNat * 0x1000000 +
    (bs.get! (off + 4)).toNat * 0x100000000 +
    (bs.get! (off + 5)).toNat * 0x10000000000 +
    (bs.get! (off + 6)).toNat * 0x1000000000000 +
    (bs.get! (off + 7)).toNat * 0x100000000000000

/-- Decode `ix.data`. The wire format starts with a u8 discriminant
    (NOT u32 like System — ComputeBudgetInstruction is a "compact"
    bincode variant with a 1-byte tag). -/
def decode (ixData : ByteArray) : ComputeBudgetIx :=
  if ixData.size = 0 then .unknown 0
  else
    let disc := (ixData.get! 0).toNat
    match disc with
    | 0 =>
      let units := readU32LE ixData 1
      let fee   := readU32LE ixData 5
      .requestUnits units fee
    | 1 => .requestHeapFrame (readU32LE ixData 1)
    | 2 => .setComputeUnitLimit (readU32LE ixData 1)
    | 3 => .setComputeUnitPrice (readU64LE ixData 1)
    | 4 => .setLoadedAccountsDataSizeLimit (readU32LE ixData 1)
    | d => .unknown d

/-- Dispatch a ComputeBudget CPI. Agave's `Entrypoint` is a no-op
    that just consumes the default 150 CU. We mirror that exactly:
    no memory mutation, `r0 := 0`, 150 CU.

    `decode` is called for spec-fidelity (so the parsed `ix` is
    well-typed) but its result is intentionally ignored — agave's
    `declare_process_instruction!(Entrypoint, 150, |_invoke_context| Ok(()))`
    likewise doesn't inspect the instruction data on CPI. -/
def dispatch (ixData : ByteArray) (_accts : List AcctInput) (mem : Mem) :
    Option NativeResult :=
  -- Discard the parsed variant — used only for spec fidelity.
  let _ := decode ixData
  some ⟨mem, 0, CU_DEFAULT⟩

end SVM.Native.ComputeBudget
