/-
  Layout-driven account codec + its aggregation — keystone #2.

  An account is a `List (Nat × FieldVal)`: each entry is a byte offset (from
  the account base) and a field value (an owned `u64`, an owned `pubkey`,
  or an opaque `blob` of byte segments). This is exactly the layout a
  Codama/Anchor IDL describes (field type → `FieldVal` kind, field order →
  offsets) — qedgen emits the per-program record; this is what its bytes
  decode to.

  `codecCoarse` is the field-atom form a spec consumes (`↦U64` / `↦Pubkey`
  / `↦Bytes`); `codecFine` is the scattered form a lift owns (dwords +
  bytes + framed gaps). `account_agg` proves them equivalent **once**,
  generically over any field list — the coarse and fine forms differ only
  at `blob` fields, which keystone #1 (`memBytesIs_segs`) bridges. The
  hand-written `src_account_eq` / `mint_account_eq` / … all become
  instances: pick the field list, this lemma does the proof.

  A field-update handler (qedgen `def fooTransition s := some {s with f := …}`)
  refines its lift by: the codec with `f` updated = the codec with one
  field-atom changed; `account_agg` reshapes coarse⟷fine; `sl_exact` closes.
  No per-program aggregation proof.
-/

import SVM.SBPF.SegAggregation
import SVM.SBPF.PubkeySL

namespace SVM.SBPF

open SVM.Pubkey

/-- A decoded account field: an owned u64, an owned pubkey (four u64
    limbs), or an opaque blob given as a byte-segment list. -/
inductive FieldVal where
  | u64    (v : Nat)
  | pubkey (p : Pubkey)
  | blob   (segs : List FieldSeg)

namespace FieldVal

/-- Coarse field atom — the form a spec/codec consumes. -/
def coarse (addr : Nat) : FieldVal → Assertion
  | .u64 v    => memU64Is addr v
  | .pubkey p => pubkeyIs addr p
  | .blob segs => memBytesIs addr (segsBytes segs)

/-- Fine field atoms — the scattered form a lift owns. Differs from
    `coarse` only on `blob`, where the `↦Bytes` blob expands to its
    segments. -/
def fine (addr : Nat) : FieldVal → Assertion
  | .u64 v    => memU64Is addr v
  | .pubkey p => pubkeyIs addr p
  | .blob segs => segsSL addr segs

/-- Side condition: a blob's owned bytes are `< 256`. -/
def fineValid : FieldVal → Prop
  | .blob segs => segsValid segs
  | _ => True

theorem coarse_fine (addr : Nat) (fv : FieldVal) (hv : fv.fineValid) :
    ∀ h, fv.coarse addr h ↔ fv.fine addr h := by
  cases fv with
  | u64 v     => intro h; exact Iff.rfl
  | pubkey p  => intro h; exact Iff.rfl
  | blob segs => exact memBytesIs_segs addr segs hv

end FieldVal

/-- Coarse account codec: separating conjunction of field atoms at their
    offsets from `base`. -/
def codecCoarse (base : Nat) : List (Nat × FieldVal) → Assertion
  | [] => emp
  | (off, fv) :: rest => fv.coarse (base + off) ** codecCoarse base rest

/-- Fine (scattered) account form. -/
def codecFine (base : Nat) : List (Nat × FieldVal) → Assertion
  | [] => emp
  | (off, fv) :: rest => fv.fine (base + off) ** codecFine base rest

/-- Every field's blob bytes are valid. -/
def codecValid : List (Nat × FieldVal) → Prop
  | [] => True
  | (_, fv) :: rest => fv.fineValid ∧ codecValid rest

/-- **Keystone #2.** A coarse account codec is equivalent to its scattered
    fine form, for any field layout. The hand-written per-account
    aggregation lemmas are instances — pick the field list. -/
theorem account_agg (base : Nat) :
    ∀ (fields : List (Nat × FieldVal)), codecValid fields →
    ∀ h, codecCoarse base fields h ↔ codecFine base fields h := by
  intro fields
  induction fields with
  | nil => intro _ h; exact Iff.rfl
  | cons hd rest ih =>
    obtain ⟨off, fv⟩ := hd
    intro hv h
    obtain ⟨hvf, hvr⟩ := hv
    show (fv.coarse (base + off) ** codecCoarse base rest) h ↔
         (fv.fine (base + off) ** codecFine base rest) h
    exact Iff.trans (sepConj_iff_congr_left _ (fv.coarse_fine (base + off) hvf) h)
      (sepConj_iff_congr_right _ (ih hvr) h)

/-! ## Validation — the SPL token account is an instance

`src_account_eq`'s content (mint pubkey, owner pubkey, amount u64, and a
`rest` blob owning bytes 72/108/109 with framed gaps) is the field list
below; `account_agg` proves the aggregation with no bespoke lemma. -/

example (base c0 c1 c2 c3 o0 o1 o2 o3 amount b72 b108 b109 : Nat) (g1 g2 : ByteArray)
    (h72 : b72 < 256) (h108 : b108 < 256) (h109 : b109 < 256) :
    ∀ h, codecCoarse base
           [ (0,  .pubkey ⟨c0, c1, c2, c3⟩),
             (32, .pubkey ⟨o0, o1, o2, o3⟩),
             (64, .u64 amount),
             (72, .blob [.byte b72, .gap g1, .byte b108, .byte b109, .gap g2]) ] h ↔
         codecFine base
           [ (0,  .pubkey ⟨c0, c1, c2, c3⟩),
             (32, .pubkey ⟨o0, o1, o2, o3⟩),
             (64, .u64 amount),
             (72, .blob [.byte b72, .gap g1, .byte b108, .byte b109, .gap g2]) ] h :=
  account_agg base _
    ⟨trivial, trivial, trivial, ⟨h72, trivial, h108, h109, trivial, trivial⟩, trivial⟩

end SVM.SBPF
