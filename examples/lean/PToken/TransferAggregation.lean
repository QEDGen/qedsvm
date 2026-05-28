/-
  Account-codec aggregation for the real p_token Transfer lift.

  The trace-guided lift owns the src/dst account fields as *scattered*
  cells: mint/owner/amount as `↦U64` (dword loads), and a few `rest`
  bytes (`ldxb` loads) with the remaining `rest` bytes framed in as
  opaque gaps. These lemmas reshape that scattered shape into the
  coarse `tokenAcctBalanceOf` codec atom `p_token_transfer_balance_spec`
  consumes — the fine→coarse step that the SL bridges
  (`memBytesIs_append`, `memBytesIs_cons_byte`, `memU64Is_eq_memBytesIs`,
  `pubkeyIs`) make mechanical.

  mint/owner/amount need NO byte aggregation: `↦Pubkey` is four `↦U64`
  limbs, matching the lift's dword cells directly. Only `rest` (a
  `↦Bytes` blob) is assembled, via `memBytesIs_cons_byte` (peel an owned
  byte) + `memBytesIs_append` (peel a framed gap).
-/

import SVM.SBPF.SepLogic
import SVM.SBPF.PubkeySL
import SVM.Solana.TokenAccountCodec

namespace Examples.PTokenTransferAggregation

open SVM.SBPF SVM.Solana

/-- Src-account `rest` layout: lift owns bytes at account offsets 72,
    108, 109; gaps `g1` (73..107, 35B) and `g2` (110..164, 55B) framed. -/
theorem src_rest_split (base b72 b108 b109 : Nat) (g1 g2 : ByteArray)
    (hg1 : g1.size = 35) (h72 : b72 < 256) (h108 : b108 < 256) (h109 : b109 < 256) :
    ∀ h, memBytesIs (base + 72)
           (PartialState.byteBA b72 ++ (g1 ++
             (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g2)))) h ↔
         ( memByteIs (base + 72) b72 ** memBytesIs (base + 73) g1 **
           memByteIs (base + 108) b108 ** memByteIs (base + 109) b109 **
           memBytesIs (base + 110) g2 ) h := by
  intro h
  rw [memBytesIs_cons_byte (base + 72) b72 _ h72 h]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  have ha := memBytesIs_append (base + 73) g1
    (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g2)) h
  rw [hg1] at ha
  rw [ha]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  rw [memBytesIs_cons_byte (base + 73 + 35) b108 _ h108 h]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  rw [memBytesIs_cons_byte (base + 73 + 35 + 1) b109 _ h109 h]

/-- Full src-account codec ↔ scattered cells. mint/owner/amount match
    the lift's `↦U64` cells directly; `rest` via `src_rest_split`. -/
theorem src_account
    (base c0 c1 c2 c3 o0 o1 o2 o3 amount b72 b108 b109 : Nat)
    (g1 g2 : ByteArray) (hg1 : g1.size = 35)
    (h72 : b72 < 256) (h108 : b108 < 256) (h109 : b109 < 256) :
    ∀ h, tokenAcctBalanceOf base
          { mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
            rest := PartialState.byteBA b72 ++ (g1 ++
              (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g2))) } h ↔
         ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
           pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
           memU64Is (base + 64) amount **
           ( memByteIs (base + 72) b72 ** memBytesIs (base + 73) g1 **
             memByteIs (base + 108) b108 ** memByteIs (base + 109) b109 **
             memBytesIs (base + 110) g2 ) ) h := by
  intro h
  simp only [tokenAcctBalanceOf, tokenAcctBalance, MINT_OFF, OWNER_OFF, AMOUNT_OFF,
    REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  exact src_rest_split base b72 b108 b109 g1 g2 hg1 h72 h108 h109 h

/-- Dst-account `rest`: lift owns only the state byte (offset 108); gaps
    `g3` (72..107, 36B) and `g4` (109..164, 56B) framed. -/
theorem dst_rest_split (base b108 : Nat) (g3 g4 : ByteArray)
    (hg3 : g3.size = 36) (h108 : b108 < 256) :
    ∀ h, memBytesIs (base + 72) (g3 ++ (PartialState.byteBA b108 ++ g4)) h ↔
         ( memBytesIs (base + 72) g3 ** memByteIs (base + 108) b108 **
           memBytesIs (base + 109) g4 ) h := by
  intro h
  have ha := memBytesIs_append (base + 72) g3 (PartialState.byteBA b108 ++ g4) h
  rw [hg3] at ha
  rw [ha]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  rw [memBytesIs_cons_byte (base + 72 + 36) b108 _ h108 h]

/-- Full dst-account codec ↔ scattered cells. The lift doesn't read the
    dst owner, so its four `↦U64` limbs are framed in (carried by
    `o0..o3`); `rest` owns only the state byte. -/
theorem dst_account
    (base c0 c1 c2 c3 o0 o1 o2 o3 amount b108 : Nat)
    (g3 g4 : ByteArray) (hg3 : g3.size = 36) (h108 : b108 < 256) :
    ∀ h, tokenAcctBalanceOf base
          { mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
            rest := g3 ++ (PartialState.byteBA b108 ++ g4) } h ↔
         ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
           pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
           memU64Is (base + 64) amount **
           ( memBytesIs (base + 72) g3 ** memByteIs (base + 108) b108 **
             memBytesIs (base + 109) g4 ) ) h := by
  intro h
  simp only [tokenAcctBalanceOf, tokenAcctBalance, MINT_OFF, OWNER_OFF, AMOUNT_OFF,
    REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  refine sepConj_iff_congr_right _ ?_ h
  intro h
  exact dst_rest_split base b108 g3 g4 hg3 h108 h

/-! ## Assertion-equality forms — for `rw` in the refinement wiring

`src_account`/`dst_account` are pointwise iffs; the refinement recipe
`rw`s them to expand the codec atoms in the goal, so we lift each to an
`Assertion` equality via `funext`+`propext`. The wiring is then:
`unfold AsmRefinesTokenTransfer; rw [src_account_eq, dst_account_eq …];
have framed := cuTripleWithinMem_frame_right F hF lift; sl_exact framed`. -/

theorem src_account_eq
    (base c0 c1 c2 c3 o0 o1 o2 o3 amount b72 b108 b109 : Nat)
    (g1 g2 : ByteArray) (hg1 : g1.size = 35)
    (h72 : b72 < 256) (h108 : b108 < 256) (h109 : b109 < 256) :
    tokenAcctBalanceOf base
      { mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
        rest := PartialState.byteBA b72 ++ (g1 ++
          (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g2))) }
      = ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
          pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
          memU64Is (base + 64) amount **
          ( memByteIs (base + 72) b72 ** memBytesIs (base + 73) g1 **
            memByteIs (base + 108) b108 ** memByteIs (base + 109) b109 **
            memBytesIs (base + 110) g2 ) ) := by
  funext h
  exact propext (src_account base c0 c1 c2 c3 o0 o1 o2 o3 amount b72 b108 b109
    g1 g2 hg1 h72 h108 h109 h)

theorem dst_account_eq
    (base c0 c1 c2 c3 o0 o1 o2 o3 amount b108 : Nat)
    (g3 g4 : ByteArray) (hg3 : g3.size = 36) (h108 : b108 < 256) :
    tokenAcctBalanceOf base
      { mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
        rest := g3 ++ (PartialState.byteBA b108 ++ g4) }
      = ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
          pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
          memU64Is (base + 64) amount **
          ( memBytesIs (base + 72) g3 ** memByteIs (base + 108) b108 **
            memBytesIs (base + 109) g4 ) ) := by
  funext h
  exact propext (dst_account base c0 c1 c2 c3 o0 o1 o2 o3 amount b108 g3 g4 hg3 h108 h)

end Examples.PTokenTransferAggregation
