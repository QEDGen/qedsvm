/-
  Generic byte-blob aggregation — the one-time keystone theorem behind
  every account-codec fine⟷coarse reshape.

  The IDL field layout (qedgen) + what the lift owns produce a
  `List FieldSeg`: each segment is an owned byte, an owned little-endian
  u64, or a framed opaque blob (gap). `memBytesIs_segs` proves, once and
  for all, that the coarse `↦Bytes` blob of those segments is equivalent
  to the separating conjunction of their fine cells. The hand-written
  per-account lemmas (`src_account_eq`, `mint_account_eq`, …) are then
  just instances — they pick a segment list; this lemma does the proof.

  Pure separation logic: no codegen, no domain knowledge. A new program's
  account aggregation is `memBytesIs_segs` applied to the segment list its
  IDL layout + lift induce.
-/

import SVM.SBPF.SepLogic

namespace SVM.SBPF

open PartialState

/-! ## Unit laws used to massage `segs` output into bespoke shapes -/

/-- Assertion-level right unit: `P ** emp = P`. The `funext` form (vs the
    pointwise `sepConj_emp_right`) lets `simp` strip a trailing `emp`
    anywhere in a sep-conj chain — needed because `segsSL` ends in `emp`. -/
theorem sepConj_emp_right_eq (P : Assertion) : (P ** emp) = P := by
  funext h; exact propext (sepConj_emp_right h)

/-- `ByteArray` right unit, to drop the trailing `++ empty` that
    `segsBytes` leaves. -/
@[simp] theorem ba_append_empty (a : ByteArray) : a ++ ByteArray.empty = a := by
  apply ByteArray.ext; simp

/-- A byte-level segment of an account field blob. -/
inductive FieldSeg where
  /-- An owned byte cell (`↦ₘ`), value `< 256`. -/
  | byte (v : Nat)
  /-- An owned little-endian u64 cell (`↦U64`). -/
  | u64  (v : Nat)
  /-- A framed opaque blob (`↦Bytes`) — bytes the lift does not read. -/
  | gap  (bs : ByteArray)

namespace FieldSeg

/-- Byte width of a segment. -/
def size : FieldSeg → Nat
  | .byte _ => 1
  | .u64 _  => 8
  | .gap bs => bs.size

/-- Byte-array realization of a segment. -/
def bytes : FieldSeg → ByteArray
  | .byte v => PartialState.byteBA v
  | .u64 v  => PartialState.u64LE v
  | .gap bs => bs

/-- Fine SL atom of a segment at `addr`. -/
def sl (addr : Nat) : FieldSeg → Assertion
  | .byte v => memByteIs addr v
  | .u64 v  => memU64Is addr v
  | .gap bs => memBytesIs addr bs

/-- Side condition: owned bytes are `< 256`. -/
def valid : FieldSeg → Prop
  | .byte v => v < 256
  | _ => True

@[simp] theorem bytes_size (s : FieldSeg) : s.bytes.size = s.size := by
  cases s <;>
    simp [bytes, size, PartialState.byteBA_size, PartialState.u64LE_size]

end FieldSeg

/-- Concatenated byte realization of a segment list (the coarse blob). -/
def segsBytes : List FieldSeg → ByteArray
  | [] => ByteArray.empty
  | s :: rest => s.bytes ++ segsBytes rest

/-- Separating conjunction of a segment list's fine cells at running
    offsets from `base`. -/
def segsSL (base : Nat) : List FieldSeg → Assertion
  | [] => emp
  | s :: rest => s.sl base ** segsSL (base + s.size) rest

/-- All owned bytes in the list are `< 256`. -/
def segsValid : List FieldSeg → Prop
  | [] => True
  | s :: rest => s.valid ∧ segsValid rest

/-- A `↦Bytes` blob of the empty byte-array owns nothing. -/
theorem memBytesIs_empty (addr : Nat) :
    memBytesIs addr ByteArray.empty = emp := by
  have hs : singletonMemBytes addr ByteArray.empty = PartialState.empty := by
    unfold singletonMemBytes PartialState.empty
    congr 1
    funext a
    have hne : ¬ (addr ≤ a ∧ a < addr + ByteArray.empty.size) := by
      simp only [ByteArray.size_empty]; omega
    exact if_neg hne
  funext h
  show (h = singletonMemBytes addr ByteArray.empty) = (h = PartialState.empty)
  rw [hs]

/-- Bridge one segment's coarse blob to its fine atom. -/
theorem seg_head_bridge (base : Nat) (s : FieldSeg) (hv : s.valid) :
    ∀ h, memBytesIs base s.bytes h ↔ s.sl base h := by
  cases s with
  | byte v => intro h; exact (memByteIs_eq_memBytesIs base v hv h).symm
  | u64 v  => intro h; exact (memU64Is_eq_memBytesIs base v h).symm
  | gap bs => intro h; exact Iff.rfl

/-- **Keystone.** The coarse `↦Bytes` blob of a segment list is
    equivalent to the separating conjunction of its fine cells. Every
    account-codec aggregation lemma is an instance of this. -/
theorem memBytesIs_segs (base : Nat) (segs : List FieldSeg)
    (hv : segsValid segs) :
    ∀ h, memBytesIs base (segsBytes segs) h ↔ segsSL base segs h := by
  induction segs generalizing base with
  | nil =>
    intro h
    show memBytesIs base ByteArray.empty h ↔ emp h
    rw [memBytesIs_empty]
  | cons s rest ih =>
    obtain ⟨hvs, hvr⟩ := hv
    intro h
    have happ := memBytesIs_append base s.bytes (segsBytes rest) h
    rw [FieldSeg.bytes_size] at happ
    show memBytesIs base (s.bytes ++ segsBytes rest) h ↔ (s.sl base ** segsSL (base + s.size) rest) h
    rw [happ]
    exact Iff.trans (sepConj_iff_congr_left _ (seg_head_bridge base s hvs) h)
      (sepConj_iff_congr_right _ (ih (base + s.size) hvr) h)

/-! ## Validation — bespoke splits are one-line instances

The hand-written `preAuth_split` (`MintAggregation`, ~30 lines: an owned
COption tag byte, a 3-byte gap, and a 32-byte authority pubkey as four
`↦U64` dwords) is the segment list `[byte, gap, u64, u64, u64, u64]`.
With the keystone it is a single application. -/

example (base b0 p0 p1 p2 p3 : Nat) (gA : ByteArray) (hb0 : b0 < 256) :
    ∀ h, memBytesIs base
           (segsBytes [.byte b0, .gap gA, .u64 p0, .u64 p1, .u64 p2, .u64 p3]) h ↔
         segsSL base [.byte b0, .gap gA, .u64 p0, .u64 p1, .u64 p2, .u64 p3] h :=
  memBytesIs_segs base _ ⟨hb0, trivial, trivial, trivial, trivial, trivial, trivial⟩

-- The SPL token-account `rest` split (owned bytes 0/36/37, framed gaps) —
-- another instance of the same lemma, no new proof.
example (base b0 b36 b37 : Nat) (g1 g2 : ByteArray)
    (hb0 : b0 < 256) (hb36 : b36 < 256) (hb37 : b37 < 256) :
    ∀ h, memBytesIs base
           (segsBytes [.byte b0, .gap g1, .byte b36, .byte b37, .gap g2]) h ↔
         segsSL base [.byte b0, .gap g1, .byte b36, .byte b37, .gap g2] h :=
  memBytesIs_segs base _ ⟨hb0, trivial, hb36, hb37, trivial, trivial⟩

end SVM.SBPF
