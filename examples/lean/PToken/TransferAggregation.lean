-- Token-account codec aggregation. MECHANICALLY EMITTED by qedlift. Do not hand-edit.

import SVM.SBPF.SegAggregation
import SVM.SBPF.PubkeySL
import SVM.Solana.TokenAccountCodec

namespace Examples.PTokenTransferAggregation

open SVM.SBPF SVM.Solana

theorem src_account_eq
    (base c0 c1 c2 c3 o0 o1 o2 o3 amount b72 b108 b109 : Nat)
    (g1 g2 : ByteArray) (hg1 : g1.size = 35) (h72 : b72 < 256) (h108 : b108 < 256) (h109 : b109 < 256) :
    tokenAcctBalanceOf base
      { mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
        rest := PartialState.byteBA b72 ++ (g1 ++ (PartialState.byteBA b108 ++ (PartialState.byteBA b109 ++ g2))) }
      = ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
          pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
          memU64Is (base + 64) amount **
          ( memByteIs (base + 72) b72 **
            memBytesIs (base + 73) g1 **
            memByteIs (base + 108) b108 **
            memByteIs (base + 109) b109 **
            memBytesIs (base + 110) g2 ) ) := by
  funext h
  apply propext
  simp only [tokenAcctBalanceOf, tokenAcctBalance, MINT_OFF, OWNER_OFF, AMOUNT_OFF,
    REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  have key := memBytesIs_segs (base + 72)
    [.byte b72, .gap g1, .byte b108, .byte b109, .gap g2]
    ⟨h72, trivial, h108, h109, trivial, trivial⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    hg1, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key

theorem dst_account_eq
    (base c0 c1 c2 c3 o0 o1 o2 o3 amount b108 : Nat)
    (g3 g4 : ByteArray) (hg3 : g3.size = 36) (h108 : b108 < 256) :
    tokenAcctBalanceOf base
      { mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
        rest := g3 ++ (PartialState.byteBA b108 ++ g4) }
      = ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
          pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
          memU64Is (base + 64) amount **
          ( memBytesIs (base + 72) g3 **
            memByteIs (base + 108) b108 **
            memBytesIs (base + 109) g4 ) ) := by
  funext h
  apply propext
  simp only [tokenAcctBalanceOf, tokenAcctBalance, MINT_OFF, OWNER_OFF, AMOUNT_OFF,
    REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  have key := memBytesIs_segs (base + 72)
    [.gap g3, .byte b108, .gap g4]
    ⟨trivial, h108, trivial, trivial⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    hg3, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key

end Examples.PTokenTransferAggregation
