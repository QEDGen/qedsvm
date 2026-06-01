/-
  Account-codec aggregation for the real p_token MintTo / Burn lifts —
  the mint account's `supply` field.

  The lift owns the mint account as scattered cells: the mint_authority
  COption tag byte (offset 0) + a 3-byte gap + the 32-byte authority
  pubkey as four `↦U64` dwords (offsets 4/12/20/28); the `supply` dword
  (offset 36); and in the tail a 1-byte decimals gap (44) + the
  `is_initialized` byte (45) + a 36-byte freeze_authority gap (46). These
  lemmas reshape that scattered shape into the coarse `mintSupplyOf` codec
  atom the MintTo/Burn refinements consume — the fine→coarse step the SL
  bridges (`memBytesIs_cons_byte`, `memBytesIs_append`,
  `memU64Is_eq_memBytesIs`) make mechanical. Mirror of `TransferAggregation`.
-/

import SVM.SBPF.SepLogic
import SVM.SBPF.PubkeySL
import SVM.Solana.MintAccountCodec
import SVM.Solana.TokenAccountCodec

namespace Examples.PTokenMintAggregation

open SVM.SBPF SVM.Solana

/-- preAuth split: COption tag byte at offset 0, 3-byte tag gap at 1, the
    32-byte authority pubkey as four `↦U64` dwords at 4/12/20/28. -/
theorem preAuth_split (base b0 p0 p1 p2 p3 : Nat) (gA : ByteArray)
    (hgA : gA.size = 3) (hb0 : b0 < 256) :
    ∀ h, memBytesIs base
           (PartialState.byteBA b0 ++ (gA ++
             (PartialState.u64LE p0 ++ (PartialState.u64LE p1 ++
               (PartialState.u64LE p2 ++ PartialState.u64LE p3))))) h ↔
         ( memByteIs base b0 ** memBytesIs (base + 1) gA **
           memU64Is (base + 4) p0 ** memU64Is (base + 12) p1 **
           memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) h := by
  intro h
  rw [memBytesIs_cons_byte base b0 _ hb0 h]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  have ha := memBytesIs_append (base + 1) gA
    (PartialState.u64LE p0 ++ (PartialState.u64LE p1 ++
      (PartialState.u64LE p2 ++ PartialState.u64LE p3))) h
  rw [hgA] at ha
  rw [ha]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  -- Peel u64LE p0 at base+1+3, convert to ↦U64.
  have h0 := memBytesIs_append (base + 1 + 3) (PartialState.u64LE p0)
    (PartialState.u64LE p1 ++ (PartialState.u64LE p2 ++ PartialState.u64LE p3)) h
  rw [PartialState.u64LE_size] at h0
  rw [h0]
  refine Iff.trans (sepConj_iff_congr_left _
    (fun h => (memU64Is_eq_memBytesIs (base + 1 + 3) p0 h).symm) h) ?_
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  -- Peel u64LE p1.
  have h1 := memBytesIs_append (base + 1 + 3 + 8) (PartialState.u64LE p1)
    (PartialState.u64LE p2 ++ PartialState.u64LE p3) h
  rw [PartialState.u64LE_size] at h1
  rw [h1]
  refine Iff.trans (sepConj_iff_congr_left _
    (fun h => (memU64Is_eq_memBytesIs (base + 1 + 3 + 8) p1 h).symm) h) ?_
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  -- Peel u64LE p2, leaving u64LE p3.
  have h2 := memBytesIs_append (base + 1 + 3 + 8 + 8) (PartialState.u64LE p2)
    (PartialState.u64LE p3) h
  rw [PartialState.u64LE_size] at h2
  rw [h2]
  refine Iff.trans (sepConj_iff_congr_left _
    (fun h => (memU64Is_eq_memBytesIs (base + 1 + 3 + 8 + 8) p2 h).symm) h) ?_
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  exact (memU64Is_eq_memBytesIs (base + 1 + 3 + 8 + 8 + 8) p3 h).symm

/-- Mint `rest` split: 1-byte decimals gap at 44, `is_initialized` byte at
    45, 36-byte freeze_authority gap at 46. -/
theorem mint_rest_split (base b45 : Nat) (gD gF : ByteArray)
    (hgD : gD.size = 1) (hb45 : b45 < 256) :
    ∀ h, memBytesIs (base + 44) (gD ++ (PartialState.byteBA b45 ++ gF)) h ↔
         ( memBytesIs (base + 44) gD ** memByteIs (base + 45) b45 **
           memBytesIs (base + 46) gF ) h := by
  intro h
  have ha := memBytesIs_append (base + 44) gD (PartialState.byteBA b45 ++ gF) h
  rw [hgD] at ha
  rw [ha]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  rw [memBytesIs_cons_byte (base + 44 + 1) b45 _ hb45 h]

/-- Full mint-account codec ↔ scattered cells. `supply` matches the lift's
    `↦U64` cell directly; `preAuth`/`rest` via the splits above. -/
theorem mint_account
    (base b0 p0 p1 p2 p3 supply b45 : Nat) (gA gD gF : ByteArray)
    (hgA : gA.size = 3) (hgD : gD.size = 1) (hb0 : b0 < 256) (hb45 : b45 < 256) :
    ∀ h, mintSupplyOf base
          { preAuth := PartialState.byteBA b0 ++ (gA ++
              (PartialState.u64LE p0 ++ (PartialState.u64LE p1 ++
                (PartialState.u64LE p2 ++ PartialState.u64LE p3)))),
            supply := supply,
            rest := gD ++ (PartialState.byteBA b45 ++ gF) } h ↔
         ( ( memByteIs base b0 ** memBytesIs (base + 1) gA **
             memU64Is (base + 4) p0 ** memU64Is (base + 12) p1 **
             memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) **
           memU64Is (base + 36) supply **
           ( memBytesIs (base + 44) gD ** memByteIs (base + 45) b45 **
             memBytesIs (base + 46) gF ) ) h := by
  intro h
  simp only [mintSupplyOf, mintAcctSupply, MINT_AUTH_OFF, SUPPLY_OFF,
    MINT_REST_OFF, Nat.add_zero]
  refine Iff.trans (sepConj_iff_congr_left _
    (preAuth_split base b0 p0 p1 p2 p3 gA hgA hb0) h) ?_
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  exact mint_rest_split base b45 gD gF hgD hb45 h

/-! ## Assertion-equality form — for `rw` in the refinement wiring -/

theorem mint_account_eq
    (base b0 p0 p1 p2 p3 supply b45 : Nat) (gA gD gF : ByteArray)
    (hgA : gA.size = 3) (hgD : gD.size = 1) (hb0 : b0 < 256) (hb45 : b45 < 256) :
    mintSupplyOf base
      { preAuth := PartialState.byteBA b0 ++ (gA ++
          (PartialState.u64LE p0 ++ (PartialState.u64LE p1 ++
            (PartialState.u64LE p2 ++ PartialState.u64LE p3)))),
        supply := supply,
        rest := gD ++ (PartialState.byteBA b45 ++ gF) }
      = ( ( memByteIs base b0 ** memBytesIs (base + 1) gA **
            memU64Is (base + 4) p0 ** memU64Is (base + 12) p1 **
            memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) **
          memU64Is (base + 36) supply **
          ( memBytesIs (base + 44) gD ** memByteIs (base + 45) b45 **
            memBytesIs (base + 46) gF ) ) := by
  funext h
  exact propext (mint_account base b0 p0 p1 p2 p3 supply b45 gA gD gF
    hgA hgD hb0 hb45 h)

/-! ## Destination token-account aggregation (MintTo / Burn)

The MintTo destination (and Burn source) token account owns two `rest`
bytes — the state byte at offset 108 *and* the byte at 109 — unlike the
Transfer dst (108 only). Hence a dedicated rest split + account form. -/

/-- Dest `rest` split: gap `g3` (36B @72), owned bytes at 108 and 109,
    gap `g4` (55B @110). -/
theorem dest_rest_split (base b108 b109 : Nat) (g3 g4 : ByteArray)
    (hg3 : g3.size = 36) (hb108 : b108 < 256) (hb109 : b109 < 256) :
    ∀ h, memBytesIs (base + 72)
           (g3 ++ (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g4))) h ↔
         ( memBytesIs (base + 72) g3 ** memByteIs (base + 108) b108 **
           memByteIs (base + 109) b109 ** memBytesIs (base + 110) g4 ) h := by
  intro h
  have ha := memBytesIs_append (base + 72) g3
    (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g4)) h
  rw [hg3] at ha
  rw [ha]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  rw [memBytesIs_cons_byte (base + 72 + 36) b108 _ hb108 h]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  rw [memBytesIs_cons_byte (base + 72 + 36 + 1) b109 _ hb109 h]

/-- Full dest-account codec ↔ scattered cells. The lift doesn't read the
    dst owner, so its four `↦U64` limbs are framed in (carried by
    `o0..o3`); `rest` owns the two bytes at 108/109. -/
theorem dest_account_eq
    (base c0 c1 c2 c3 o0 o1 o2 o3 amount b108 b109 : Nat)
    (g3 g4 : ByteArray) (hg3 : g3.size = 36) (hb108 : b108 < 256) (hb109 : b109 < 256) :
    tokenAcctBalanceOf base
      { mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
        rest := g3 ++ (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g4)) }
      = ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
          pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
          memU64Is (base + 64) amount **
          ( memBytesIs (base + 72) g3 ** memByteIs (base + 108) b108 **
            memByteIs (base + 109) b109 ** memBytesIs (base + 110) g4 ) ) := by
  funext h
  apply propext
  simp only [tokenAcctBalanceOf, tokenAcctBalance, MINT_OFF, OWNER_OFF, AMOUNT_OFF,
    REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  exact dest_rest_split base b108 b109 g3 g4 hg3 hb108 hb109 h

end Examples.PTokenMintAggregation
