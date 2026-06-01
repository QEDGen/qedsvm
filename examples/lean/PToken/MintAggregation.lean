/-
  Account-codec aggregation for the real p_token MintTo / Burn lifts —
  the mint account's `supply` field (and the dest/source token account).

  The lift owns the mint account as scattered cells: the mint_authority
  COption tag byte (offset 0) + a 3-byte gap + the 32-byte authority
  pubkey as four `↦U64` dwords (4/12/20/28); the `supply` dword (36); and
  a 1-byte decimals gap (44) + the `is_initialized` byte (45) + a 36-byte
  freeze_authority gap (46). These lemmas reshape that into the coarse
  `mintSupplyOf` codec atom the MintTo/Burn refinements consume.

  Each `↦Bytes` blob split is now a one-application instance of the
  keystone `memBytesIs_segs` (`SVM/SBPF/SegAggregation.lean`): pick the
  byte-segment list, the keystone does the proof.
-/

import SVM.SBPF.SegAggregation
import SVM.SBPF.PubkeySL
import SVM.Solana.MintAccountCodec
import SVM.Solana.TokenAccountCodec

namespace Examples.PTokenMintAggregation

open SVM.SBPF SVM.Solana

/-- Full mint-account codec ↔ scattered cells. `supply` matches the lift's
    `↦U64` cell directly; `preAuth` (tag byte + 3-byte gap + 32-byte
    authority pubkey as four `↦U64` dwords) and `rest` (decimals gap +
    is_init byte + freeze gap) split via `memBytesIs_segs`. -/
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
  apply propext
  simp only [mintSupplyOf, mintAcctSupply, MINT_AUTH_OFF, SUPPLY_OFF,
    MINT_REST_OFF, Nat.add_zero]
  have keyP : ∀ h, memBytesIs base
      (PartialState.byteBA b0 ++ (gA ++ (PartialState.u64LE p0 ++
        (PartialState.u64LE p1 ++ (PartialState.u64LE p2 ++ PartialState.u64LE p3))))) h ↔
      ( memByteIs base b0 ** memBytesIs (base + 1) gA ** memU64Is (base + 4) p0 **
        memU64Is (base + 12) p1 ** memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) h := by
    intro h
    have key := memBytesIs_segs base
      [.byte b0, .gap gA, .u64 p0, .u64 p1, .u64 p2, .u64 p3]
      ⟨hb0, trivial, trivial, trivial, trivial, trivial, trivial⟩ h
    simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
      hgA, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
    exact key
  refine Iff.trans (sepConj_iff_congr_left _ keyP h) ?_
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  have key := memBytesIs_segs (base + 44)
    [.gap gD, .byte b45, .gap gF] ⟨trivial, hb45, trivial, trivial⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    hgD, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key

/-- Mint codec ↔ scattered cells when the lift reads *only* `supply` and
    the `is_initialized` byte (the Burn pattern): the whole 36-byte
    `preAuth` blob is framed opaque, `supply` matches the lift's dword,
    and `rest` splits into a 1-byte decimals gap + the is_init byte + a
    36-byte freeze gap. -/
theorem mint_supply_eq
    (base supply b45 : Nat) (preAuth gD gF : ByteArray)
    (hgD : gD.size = 1) (hb45 : b45 < 256) :
    mintSupplyOf base
      { preAuth := preAuth, supply := supply,
        rest := gD ++ (PartialState.byteBA b45 ++ gF) }
      = ( memBytesIs base preAuth **
          memU64Is (base + 36) supply **
          ( memBytesIs (base + 44) gD ** memByteIs (base + 45) b45 **
            memBytesIs (base + 46) gF ) ) := by
  funext h
  apply propext
  simp only [mintSupplyOf, mintAcctSupply, MINT_AUTH_OFF, SUPPLY_OFF,
    MINT_REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  have key := memBytesIs_segs (base + 44)
    [.gap gD, .byte b45, .gap gF] ⟨trivial, hb45, trivial, trivial⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    hgD, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key

/-! ## Destination token-account aggregation (MintTo / Burn)

The MintTo destination (and Burn source) token account owns two `rest`
bytes — the state byte at 108 *and* the byte at 109 — unlike the Transfer
dst (108 only). -/

/-- Full dest-account codec ↔ scattered cells. The lift doesn't read the
    dst owner, so its four `↦U64` limbs are framed in (carried by
    `o0..o3`); `rest` owns the two bytes at 108/109 (gaps `g3` @72,
    `g4` @110). -/
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
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  have key := memBytesIs_segs (base + 72)
    [.gap g3, .byte b108, .byte b109, .gap g4]
    ⟨trivial, hb108, hb109, trivial, trivial⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    hg3, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key

end Examples.PTokenMintAggregation
