-- The Solana ComputeBudget program — native, not BPF.
--
-- agave's `Entrypoint` is `declare_process_instruction!(Entrypoint, 150,
-- |_| Ok(()))`: charge 150 CU, succeed, no state mutation. Real semantics
-- are transaction-level (budget/data-size sizing), out of scope for
-- per-instruction qedsvm (Tier 4). We model only the CPI path: an
-- `invoke(&compute_budget_ix)` sees `r0 = 0` and 150 CU, matching agave.

import SVM.Native.AcctInput

namespace SVM.Native.ComputeBudget

open SVM.SBPF.Memory
open SVM.Native

/-- ComputeBudget program-id (`ComputeBudget111111111111111111111111111111`),
    base58-decoded and encoded little-endian as a `Nat`. -/
def PROGRAM_ID : Nat :=
  0x000000403a9b432c6b12f7c5bbe58cbce79bc372baadecff321721e56f460603

/-- `DEFAULT_COMPUTE_UNITS` from `solana-compute-budget-program/src/lib.rs`;
    flat for every variant. -/
def CU_DEFAULT : Nat := 150

/-! ## ComputeBudgetInstruction enum

Mirrors agave's `ComputeBudgetInstruction`. Decoded for spec fidelity;
`dispatch` treats every variant the same (no-op + 150 CU) per agave's CPI. -/

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

/-- Decode `ix.data`. Wire format leads with a u8 discriminant (NOT u32
    like System — this enum uses a compact 1-byte tag). -/
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

/-- Dispatch a ComputeBudget CPI: no memory mutation, `r0 := 0`, 150 CU,
    mirroring agave's no-op `Entrypoint`. `decode` runs for spec fidelity
    but its result is intentionally ignored (agave likewise doesn't inspect
    instruction data on CPI). -/
def dispatch (ixData : ByteArray) (_accts : List AcctInput) (mem : Mem) :
    Option NativeResult :=
  let _ := decode ixData
  some ⟨mem, 0, CU_DEFAULT⟩

end SVM.Native.ComputeBudget
