/-
  Generalization test — the reusable proof library against a NON-token
  program (a multisig vault, from qedgen's `examples/rust/multisig`).

  This validates that the two keystones (`memBytesIs_segs`, `account_agg`)
  + the `FieldVal` codec generalize beyond the SPL token/mint layouts —
  to a layout with `u8` fields, a `Pubkey`, and array blobs — with NO new
  proof: the multisig account aggregation is a single `account_agg`
  application, and a field-update effect (`approve`: `approval_count += 1`)
  is a single-field codec change, exactly the refinement shape.

  Account layout (`programs/src/state.rs`, packed):
    creator       : Pubkey  @ 0
    threshold     : u8      @ 32
    member_count  : u8      @ 33
    members       : [Pubkey; 32] @ 34   (1024 B)
    voted         : [u8; 32]     @ 1058 (32 B)
    approval_count: u8      @ 1090
    rejection_count: u8     @ 1091
    bump          : u8      @ 1092
    status        : u8      @ 1093

  This is the PROOF-LIBRARY half of the pipeline. The other half —
  qedlift lifting the multisig's bytecode — is a separate executor-coverage
  question (array indexing + signer syscalls), independent of the library
  tested here.
-/

import SVM.SBPF.AccountCodec

namespace Examples.MultisigGeneralization

open SVM.SBPF SVM.Pubkey

/-- The multisig account as a `FieldVal` layout. `members` / `voted` carry
    their byte segments (the voter's owned slot + framed gaps the lift
    induces); the scalar fields are direct `byte`/`pubkey` atoms. -/
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

/-- **Generalization holds.** The multisig account codec ⟷ scattered cells
    is one `account_agg` application — no new aggregation lemma, despite a
    non-token layout (u8 fields + a pubkey + array blobs). The blob
    side-conditions (owned bytes `< 256`) are the only hypotheses. -/
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

/-- The `approve` effect (`approval_count += 1`) is a single-field change:
    the pre and post codecs differ only in the `approval_count` atom at
    offset 1090 — exactly what a refinement's `sl_exact` matches against a
    lift that writes that one byte. Everything else (creator, members,
    voted, …) flows through. The witness here keeps `voted`/`status`
    abstract; a full refinement would also reflect `voted[i] := 1`. -/
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
