/-
  Generic byte-blob aggregation — the one-time keystone theorem behind
  every account-codec fine⟷coarse reshape.

  IDL field layout + lift ownership yield a `List FieldSeg` (owned byte /
  owned LE u64 / framed opaque gap). `memBytesIs_segs` proves once and for
  all that the coarse `↦Bytes` blob equals the separating conjunction of
  the fine cells; the per-account lemmas are instances picking a segment
  list. Pure separation logic, no codegen or domain knowledge.
-/

import SVM.SBPF.SepLogic

namespace SVM.SBPF

open PartialState

/-! ## Unit laws used to massage `segs` output into bespoke shapes -/

/-- Assertion-level right unit `P ** emp = P`. The `funext` form (vs
    pointwise `sepConj_emp_right`) lets `simp` strip a trailing `emp`
    anywhere in a chain — needed since `segsSL` ends in `emp`. -/
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

The hand-written `preAuth_split` (~30 lines: COption tag byte, 3-byte
gap, 32-byte authority as four dwords) is the segment list
`[byte, gap, u64, u64, u64, u64]` — one keystone application. -/

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

/-! ## Byte-granular `↦U64` bridge (qedlift hot regions — H8 Phase B)

When a program touches overlapping bytes at MIXED widths (e.g. pinocchio
reading `input[0]` as a byte AND `input[0..8)` as a dword), qedlift
demotes the region to per-byte atoms and the wide access reshapes through
this bridge: 8 adjacent `↦ₘ` atoms = one `↦U64` of their LE Horner
combination. -/

set_option maxHeartbeats 1600000 in
/-- Eight adjacent byte atoms ↔ one `↦U64` of their LE Horner combination.
    Keystone instance over `[.byte b0, …, .byte b7]` + the u64LE-of-Horner
    byte computation. (Heartbeats: high-byte `omega` carries `256^7`
    coefficients.) -/
theorem byte_atoms_eq_memU64Is (a b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    ∀ h,
      ((a ↦ₘ b0) ** ((a + 1) ↦ₘ b1) ** ((a + 2) ↦ₘ b2) **
       ((a + 3) ↦ₘ b3) ** ((a + 4) ↦ₘ b4) ** ((a + 5) ↦ₘ b5) **
       ((a + 6) ↦ₘ b6) ** ((a + 7) ↦ₘ b7)) h
      ↔ memU64Is a
          (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
            (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) h := by
  intro h
  have hsegs := memBytesIs_segs a
      [.byte b0, .byte b1, .byte b2, .byte b3,
       .byte b4, .byte b5, .byte b6, .byte b7]
      ⟨h0, h1, h2, h3, h4, h5, h6, h7, trivial⟩ h
  -- The blob is the `u64LE` of the Horner combination (each byte-extraction
  -- collapses by `omega` under the `< 256` bounds).
  have hba : segsBytes
      [.byte b0, .byte b1, .byte b2, .byte b3,
       .byte b4, .byte b5, .byte b6, .byte b7]
      = PartialState.u64LE
          (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
            (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) := by
    have e0 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) % 256 = b0 := by omega
    have e1 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) / 0x100 % 256 = b1 := by
      omega
    have e2 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) / 0x10000 % 256 = b2 := by
      omega
    have e3 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) / 0x1000000 % 256
        = b3 := by omega
    have e4 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) / 0x100000000 % 256
        = b4 := by omega
    have e5 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) / 0x10000000000 % 256
        = b5 := by omega
    have e6 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) / 0x1000000000000 % 256
        = b6 := by omega
    have e7 : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
        (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) / 0x100000000000000 % 256
        = b7 := by omega
    show (⟨#[b0.toUInt8, b1.toUInt8, b2.toUInt8, b3.toUInt8,
             b4.toUInt8, b5.toUInt8, b6.toUInt8, b7.toUInt8]⟩ : ByteArray)
        = _
    simp only [PartialState.u64LE, e0, e1, e2, e3, e4, e5, e6, e7]
  rw [hba] at hsegs
  rw [memU64Is_eq_memBytesIs a _ h, hsegs]
  -- Both sides are now byte-atom sepConjs; the keystone's RHS accumulated
  -- `+ 1 + 1 …` addresses and a trailing `** emp`.
  show _ ↔ ((a ↦ₘ b0) ** ((a + 1) ↦ₘ b1) ** ((a + 1 + 1) ↦ₘ b2) **
       ((a + 1 + 1 + 1) ↦ₘ b3) ** ((a + 1 + 1 + 1 + 1) ↦ₘ b4) **
       ((a + 1 + 1 + 1 + 1 + 1) ↦ₘ b5) **
       ((a + 1 + 1 + 1 + 1 + 1 + 1) ↦ₘ b6) **
       (((a + 1 + 1 + 1 + 1 + 1 + 1 + 1) ↦ₘ b7) ** emp)) h
  rw [sepConj_emp_right_eq,
      show a + 1 + 1 = a + 2 from by omega,
      show a + 1 + 1 + 1 = a + 3 from by omega,
      show a + 1 + 1 + 1 + 1 = a + 4 from by omega,
      show a + 1 + 1 + 1 + 1 + 1 = a + 5 from by omega,
      show a + 1 + 1 + 1 + 1 + 1 + 1 = a + 6 from by omega,
      show a + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a + 7 from by omega]

set_option maxHeartbeats 400000 in
/-- Four adjacent byte atoms ↔ one `↦U32` cell of their LE Horner
    combination — the word-width sibling of `byte_atoms_eq_memU64Is`
    (H8 Phase B-2: `stw`/`ldxw` over byte-demoted regions). -/
theorem byte_atoms_eq_memU32Is (a b0 b1 b2 b3 : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    ∀ h,
      ((a ↦ₘ b0) ** ((a + 1) ↦ₘ b1) ** ((a + 2) ↦ₘ b2) **
       ((a + 3) ↦ₘ b3)) h
      ↔ memU32Is a (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) h := by
  intro h
  have hsegs := memBytesIs_segs a
      [.byte b0, .byte b1, .byte b2, .byte b3]
      ⟨h0, h1, h2, h3, trivial⟩ h
  have hba : segsBytes [.byte b0, .byte b1, .byte b2, .byte b3]
      = PartialState.u32LE
          (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) := by
    have e0 : (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) % 256 = b0 := by
      omega
    have e1 : (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 0x100 % 256
        = b1 := by omega
    have e2 : (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 0x10000 % 256
        = b2 := by omega
    have e3 : (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 0x1000000 % 256
        = b3 := by omega
    show (⟨#[b0.toUInt8, b1.toUInt8, b2.toUInt8, b3.toUInt8]⟩ : ByteArray)
        = _
    simp only [PartialState.u32LE, e0, e1, e2, e3]
  rw [hba] at hsegs
  rw [memU32Is_eq_memBytesIs a _ h, hsegs]
  show _ ↔ ((a ↦ₘ b0) ** ((a + 1) ↦ₘ b1) ** ((a + 1 + 1) ↦ₘ b2) **
       (((a + 1 + 1 + 1) ↦ₘ b3) ** emp)) h
  rw [sepConj_emp_right_eq,
      show a + 1 + 1 = a + 2 from by omega,
      show a + 1 + 1 + 1 = a + 3 from by omega]

end SVM.SBPF
