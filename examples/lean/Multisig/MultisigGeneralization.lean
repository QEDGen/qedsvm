/-
  Generalization test: memBytesIs_segs + account_agg + FieldVal codec work on a
  non-token layout (multisig vault, u8 fields + Pubkey + array blobs) with no new proof.
  Layout (programs/src/state.rs, packed): creator@0, threshold@32, member_count@33,
  members[Pubkey;32]@34, voted[u8;32]@1058, approval_count@1090, rejection_count@1091,
  bump@1092, status@1093. Bytecode lifting (array indexing + signer syscalls) is separate.
-/

import SVM.SBPF.AccountCodec

namespace Examples.MultisigGeneralization

open SVM.SBPF SVM.Pubkey

/-- Multisig account as a FieldVal list. Blob fields carry FieldSeg lists; scalars are byte/pubkey atoms. -/
def msigFields
    (creator : Pubkey) (threshold memberCount approval rejection bump status : Nat)
    (membersSegs votedSegs : List FieldSeg) : List (Nat × FieldVal) :=
  [ (0,    .pubkey creator),
    (32,   .byte threshold),
    (33,   .byte memberCount),
    (34,   .blob membersSegs),
    (1058, .blob votedSegs),
    (1090, .byte approval),
    (1091, .byte rejection),
    (1092, .byte bump),
    (1093, .byte status) ]

/-- Multisig codecCoarse ↔ codecFine via one account_agg call — no new aggregation lemma. -/
theorem msig_account_agg
    (base : Nat) (creator : Pubkey)
    (threshold memberCount approval rejection bump status : Nat)
    (membersSegs votedSegs : List FieldSeg)
    (hm : segsValid membersSegs) (hv : segsValid votedSegs) :
    ∀ h, codecCoarse base
           (msigFields creator threshold memberCount approval rejection bump status
             membersSegs votedSegs) h ↔
         codecFine base
           (msigFields creator threshold memberCount approval rejection bump status
             membersSegs votedSegs) h :=
  account_agg base _
    ⟨trivial, trivial, trivial, hm, hv, trivial, trivial, trivial, trivial, trivial⟩

/-- codecCoarse unfolds to the scattered-cells form — the approve refinement target shape. -/
example (base : Nat) (creator : Pubkey)
    (threshold memberCount approval rejection bump status : Nat)
    (membersSegs votedSegs : List FieldSeg) :
    codecCoarse base
        (msigFields creator threshold memberCount approval rejection bump status
          membersSegs votedSegs)
      = ( (base ↦Pubkey creator) ** (base + 32 ↦ₘ threshold) ** (base + 33 ↦ₘ memberCount) **
          (base + 34 ↦Bytes segsBytes membersSegs) ** (base + 1058 ↦Bytes segsBytes votedSegs) **
          (base + 1090 ↦ₘ approval) ** (base + 1091 ↦ₘ rejection) **
          (base + 1092 ↦ₘ bump) ** (base + 1093 ↦ₘ status) ** emp ) := by
  rfl

end Examples.MultisigGeneralization
