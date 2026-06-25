/-
  `holdsFor` ↔ memory-read bridges for `codecCoarse` field atoms (issue #48).

  The qedgen↔qedsvm discharge bridge relates two equivalent-but-syntactically
  different state↔memory encodings:

  - qedgen's `qedbridge` `encodeState` is a flat read-conjunction
    `readU64 mem (addr+off) = s.field ∧ …`;
  - qedlift's refinement post is `holdsFor (codecCoarse base postFields)`, which
    recurses to `fv.coarse (base+off) ** …`.

  This file provides the missing byte-level bridge, per field type, plus the
  `**`-decomposition that exposes a coarse codec as its per-field atoms.

  ## The bridge is asymmetric — do not state it as a bare `↔`

  - **Forward (`holdsFor → read`) is unconditional** for the U64/pubkey atoms:
    the `holdsFor` witness is the singleton, whose bytes are canonical by
    construction, so `readU64` recovers `v % 2^64` directly. (`memByteIs` stores
    its value RAW, so its forward read is `readU8 … = v % 256`.)
  - **Reverse (`read → holdsFor`) needs byte-canonicality.** `readU64 = v % 2^64`
    only pins each `s.mem (a+i) % 256`; reconstructing the singleton's
    `CompatibleWith` needs `s.mem (a+i) = byteᵢ` *raw*, which fails on a
    non-canonical cell (≥ 256). That precondition is exactly the L3 fence
    `StateBounded.mem_lt : ∀ a, s.mem a < 256` (`SVM/SBPF/Bounded.lean`), so the
    reverse lemmas take that hypothesis and ship `…_of_bounded` wrappers.

  The disjoint-union *build* direction of the codec corollary (read-conjunction
  → `holdsFor (codecCoarse …)`, "build the pre from `encodeState`") additionally
  needs an offset-non-overlap predicate (`layoutDisjoint`, kept separate from
  `codecValid`) to reassemble the `**` witness.  `holdsFor_codecCoarse_of_reads`
  delivers it for every field kind (byte/u64/pubkey + opaque blob).  So this
  file provides the per-atom bridges both ways, plus the codec corollary both
  ways.
-/

import SVM.SBPF.AccountCodec
import SVM.SBPF.Bounded

namespace SVM.SBPF

open SVM.Pubkey Memory PartialState

/-! ## `CompatibleWith` / `holdsFor` split helpers

Decompose a `holdsFor` of a separating conjunction into `holdsFor` of each
conjunct.  These lose the disjointness witness (fine for read-recovery, which
never needs the partial state back). -/

/-- The left half of a compatible union is compatible (left-biased union, no
    disjointness needed). -/
theorem compatibleWith_union_left {h1 h2 : PartialState} {s : State}
    (h : (h1.union h2).CompatibleWith s) : h1.CompatibleWith s where
  regs := fun r v hr => h.regs r v (union_regs_of_left_some hr)
  mem  := fun a v ha => h.mem a v (union_mem_of_left_some ha)
  pc   := fun v hv => h.pc v (union_pc_of_left_some hv)
  returnData := fun rd hrd => h.returnData rd (union_returnData_of_left_some hrd)
  callStack := fun cs hcs => h.callStack cs (union_callStack_of_left_some hcs)

/-- The right half of a *disjoint* compatible union is compatible. -/
theorem compatibleWith_union_right {h1 h2 : PartialState} {s : State}
    (hd : h1.Disjoint h2) (h : (h1.union h2).CompatibleWith s) :
    h2.CompatibleWith s where
  regs := fun r v hr => h.regs r v (by
    rcases hd.regs r with hn | hn
    · rw [union_regs_of_left_none hn]; exact hr
    · rw [hr] at hn; exact absurd hn (by simp))
  mem := fun a v ha => h.mem a v (by
    rcases hd.mem a with hn | hn
    · rw [union_mem_of_left_none hn]; exact ha
    · rw [ha] at hn; exact absurd hn (by simp))
  pc := fun v hv => h.pc v (by
    rcases hd.pc with hn | hn
    · rw [union_pc_of_left_none hn]; exact hv
    · rw [hv] at hn; exact absurd hn (by simp))
  returnData := fun rd hrd => h.returnData rd (by
    rcases hd.returnData with hn | hn
    · rw [union_returnData_of_left_none hn]; exact hrd
    · rw [hrd] at hn; exact absurd hn (by simp))
  callStack := fun cs hcs => h.callStack cs (by
    rcases hd.callStack with hn | hn
    · rw [union_callStack_of_left_none hn]; exact hcs
    · rw [hcs] at hn; exact absurd hn (by simp))

/-- `holdsFor` of a `**` projects onto its left conjunct. -/
theorem holdsFor_sepConj_left {P Q : Assertion} {s : State}
    (h : (P ** Q).holdsFor s) : P.holdsFor s := by
  obtain ⟨hh, hc, h1, h2, _, hu, hP, _⟩ := h
  subst hu
  exact ⟨h1, compatibleWith_union_left hc, hP⟩

/-- `holdsFor` of a `**` projects onto its right conjunct. -/
theorem holdsFor_sepConj_right {P Q : Assertion} {s : State}
    (h : (P ** Q).holdsFor s) : Q.holdsFor s := by
  obtain ⟨hh, hc, h1, h2, hd, hu, _, hQ⟩ := h
  subst hu
  exact ⟨h2, compatibleWith_union_right hd hc, hQ⟩

/-! ## Forward bridges (`holdsFor` → read), unconditional -/

/-- A `↦ₘ` cell exposes its raw memory byte. -/
theorem mem_of_holdsFor_memByteIs {a v : Nat} {s : State}
    (h : (memByteIs a v).holdsFor s) : s.mem a = v := by
  obtain ⟨hh, hc, heq⟩ := h
  have heq' : hh = singletonMem a v := heq
  subst heq'
  exact hc.mem a v singletonMem_mem_self

/-- A `↦ₘ` cell decodes to `readU8 … = v % 256` (the `% 256` is the byte's normal
    form, since `singletonMem` stores `v` raw). -/
theorem readU8_of_holdsFor_memByteIs {a v : Nat} {s : State}
    (h : (memByteIs a v).holdsFor s) : readU8 s.mem a = v % 256 := by
  unfold readU8
  rw [mem_of_holdsFor_memByteIs h]

/-- A `↦U64` cell decodes to `readU64 … = v % 2^64`. -/
theorem readU64_of_holdsFor_memU64Is {a v : Nat} {s : State}
    (h : (memU64Is a v).holdsFor s) : readU64 s.mem a = v % 2 ^ 64 := by
  obtain ⟨hh, hc, heq⟩ := h
  have heq' : hh = singletonMemU64 a v := heq
  subst heq'
  have e0 := hc.mem a _ (singletonMemU64_mem_0 a v)
  have e1 := hc.mem (a + 1) _ (singletonMemU64_mem_1 a v)
  have e2 := hc.mem (a + 2) _ (singletonMemU64_mem_2 a v)
  have e3 := hc.mem (a + 3) _ (singletonMemU64_mem_3 a v)
  have e4 := hc.mem (a + 4) _ (singletonMemU64_mem_4 a v)
  have e5 := hc.mem (a + 5) _ (singletonMemU64_mem_5 a v)
  have e6 := hc.mem (a + 6) _ (singletonMemU64_mem_6 a v)
  have e7 := hc.mem (a + 7) _ (singletonMemU64_mem_7 a v)
  unfold readU64
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  omega

/-- A `↦Pubkey` atom decodes to the four-limb `pubkeyAt` read-conjunction (the
    form `encodeState`/`readPubkey` already use).  Forward needs each limb
    `< 2^64` — true for any pubkey read out of memory. -/
theorem pubkeyAt_of_holdsFor_pubkeyIs {base : Nat} {pk : Pubkey} {s : State}
    (hb0 : pk.c0 < 2 ^ 64) (hb1 : pk.c1 < 2 ^ 64)
    (hb2 : pk.c2 < 2 ^ 64) (hb3 : pk.c3 < 2 ^ 64)
    (h : (pubkeyIs base pk).holdsFor s) : pubkeyAt s.mem base pk := by
  unfold pubkeyIs at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [readU64_of_holdsFor_memU64Is (holdsFor_sepConj_left h)]
    exact Nat.mod_eq_of_lt hb0
  · rw [readU64_of_holdsFor_memU64Is (holdsFor_sepConj_left (holdsFor_sepConj_right h))]
    exact Nat.mod_eq_of_lt hb1
  · rw [readU64_of_holdsFor_memU64Is
        (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right h)))]
    exact Nat.mod_eq_of_lt hb2
  · rw [readU64_of_holdsFor_memU64Is
        (holdsFor_sepConj_right (holdsFor_sepConj_right (holdsFor_sepConj_right h)))]
    exact Nat.mod_eq_of_lt hb3

/-! ## Reverse bridges (read → `holdsFor`), byte-canonicality-gated

The witness is the singleton; the only obligation is its `CompatibleWith`, which
reduces to one raw byte-equality per owned cell.  Each is recovered from the read
plus canonicality (`s.mem … < 256`). -/

/-- Build `CompatibleWith` for a single-byte singleton from its byte value. -/
theorem compatibleWith_singletonMem {a v : Nat} {s : State} (h : s.mem a = v) :
    (singletonMem a v).CompatibleWith s where
  regs := fun r v' hr => by simp at hr
  mem := fun a' v' ha' => by
    by_cases hxa : a' = a
    · subst hxa
      rw [singletonMem_mem_self] at ha'
      injection ha' with e; rw [← e]; exact h
    · rw [singletonMem_mem_other hxa] at ha'; simp at ha'
  pc := fun v' hv' => by simp at hv'
  returnData := fun rd hrd => by simp at hrd
  callStack := fun cs hcs => by simp at hcs

/-- Build `CompatibleWith` for a U64 singleton from its eight LE byte values. -/
theorem compatibleWith_singletonMemU64 {a v : Nat} {s : State}
    (h0 : s.mem a = v % 256)
    (h1 : s.mem (a + 1) = v / 0x100 % 256)
    (h2 : s.mem (a + 2) = v / 0x10000 % 256)
    (h3 : s.mem (a + 3) = v / 0x1000000 % 256)
    (h4 : s.mem (a + 4) = v / 0x100000000 % 256)
    (h5 : s.mem (a + 5) = v / 0x10000000000 % 256)
    (h6 : s.mem (a + 6) = v / 0x1000000000000 % 256)
    (h7 : s.mem (a + 7) = v / 0x100000000000000 % 256) :
    (singletonMemU64 a v).CompatibleWith s where
  regs := fun r v' hr => by simp at hr
  mem := fun a' v' ha' => by
    rcases Nat.lt_or_ge a' a with hlo | _
    · rw [singletonMemU64_mem_outside a v a' (Or.inl hlo)] at ha'; simp at ha'
    rcases Nat.lt_or_ge a' (a + 1) with h | _
    · have e : a' = a := by omega
      subst e; rw [singletonMemU64_mem_0] at ha'
      injection ha' with e'; rw [← e']; exact h0
    rcases Nat.lt_or_ge a' (a + 2) with h | _
    · have e : a' = a + 1 := by omega
      subst e; rw [singletonMemU64_mem_1] at ha'
      injection ha' with e'; rw [← e']; exact h1
    rcases Nat.lt_or_ge a' (a + 3) with h | _
    · have e : a' = a + 2 := by omega
      subst e; rw [singletonMemU64_mem_2] at ha'
      injection ha' with e'; rw [← e']; exact h2
    rcases Nat.lt_or_ge a' (a + 4) with h | _
    · have e : a' = a + 3 := by omega
      subst e; rw [singletonMemU64_mem_3] at ha'
      injection ha' with e'; rw [← e']; exact h3
    rcases Nat.lt_or_ge a' (a + 5) with h | _
    · have e : a' = a + 4 := by omega
      subst e; rw [singletonMemU64_mem_4] at ha'
      injection ha' with e'; rw [← e']; exact h4
    rcases Nat.lt_or_ge a' (a + 6) with h | _
    · have e : a' = a + 5 := by omega
      subst e; rw [singletonMemU64_mem_5] at ha'
      injection ha' with e'; rw [← e']; exact h5
    rcases Nat.lt_or_ge a' (a + 7) with h | _
    · have e : a' = a + 6 := by omega
      subst e; rw [singletonMemU64_mem_6] at ha'
      injection ha' with e'; rw [← e']; exact h6
    rcases Nat.lt_or_ge a' (a + 8) with h | hge
    · have e : a' = a + 7 := by omega
      subst e; rw [singletonMemU64_mem_7] at ha'
      injection ha' with e'; rw [← e']; exact h7
    · rw [singletonMemU64_mem_outside a v a' (Or.inr hge)] at ha'; simp at ha'
  pc := fun v' hv' => by simp at hv'
  returnData := fun rd hrd => by simp at hrd
  callStack := fun cs hcs => by simp at hcs

/-- Reverse of `readU8_of_holdsFor_memByteIs`: a canonical byte read rebuilds the
    `↦ₘ` atom. -/
theorem holdsFor_memByteIs_of_read {a v : Nat} {s : State}
    (hc : s.mem a < 256) (hr : readU8 s.mem a = v) :
    (memByteIs a v).holdsFor s := by
  refine ⟨singletonMem a v, compatibleWith_singletonMem ?_, rfl⟩
  unfold readU8 at hr
  omega

/-- Reverse of `readU64_of_holdsFor_memU64Is`: a canonical 8-byte read rebuilds
    the `↦U64` atom. -/
theorem holdsFor_memU64Is_of_read {a v : Nat} {s : State}
    (hc : ∀ x, s.mem x < 256) (hr : readU64 s.mem a = v % 2 ^ 64) :
    (memU64Is a v).holdsFor s := by
  have c0 := hc a; have c1 := hc (a + 1); have c2 := hc (a + 2); have c3 := hc (a + 3)
  have c4 := hc (a + 4); have c5 := hc (a + 5); have c6 := hc (a + 6); have c7 := hc (a + 7)
  unfold readU64 at hr
  refine ⟨singletonMemU64 a v,
    compatibleWith_singletonMemU64 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- `StateBounded` wrapper for the single-byte reverse bridge. -/
theorem holdsFor_memByteIs_of_read_bounded {a v : Nat} {s : State}
    (hb : StateBounded s) (hr : readU8 s.mem a = v) :
    (memByteIs a v).holdsFor s :=
  holdsFor_memByteIs_of_read (hb.mem_lt a) hr

/-- `StateBounded` wrapper for the U64 reverse bridge. -/
theorem holdsFor_memU64Is_of_read_bounded {a v : Nat} {s : State}
    (hb : StateBounded s) (hr : readU64 s.mem a = v % 2 ^ 64) :
    (memU64Is a v).holdsFor s :=
  holdsFor_memU64Is_of_read hb.mem_lt hr

/-! ## codecCoarse forward corollary

`holdsFor` of a coarse account codec decomposes into `holdsFor` of each field's
coarse atom — the layout-general `**` peel.  Compose with the per-atom forward
bridges above to land the per-field read-conjunction `encodeState` expects.  No
disjointness/non-overlap hypothesis is needed in this direction: the witness
already carries it. -/

theorem holdsFor_codecCoarse_field {base : Nat} {s : State} :
    ∀ (fields : List (Nat × FieldVal)) {off : Nat} {fv : FieldVal},
      (codecCoarse base fields).holdsFor s → (off, fv) ∈ fields →
      (fv.coarse (base + off)).holdsFor s := by
  intro fields
  induction fields with
  | nil => intro off fv _ hmem; simp at hmem
  | cons hd rest ih =>
    obtain ⟨o, f⟩ := hd
    intro off fv h hmem
    simp only [codecCoarse] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      exact holdsFor_sepConj_left h
    · exact ih (holdsFor_sepConj_right h) htl

/-! ## codecCoarse reverse reassembly (issue #48, Option A: scalar layouts)

The "build the pre from `encodeState`" direction: given the per-field reads, byte
canonicality, and a pairwise offset-non-overlap predicate, rebuild
`holdsFor (codecCoarse base fields) s`.  Restricted here to scalar fields
(`byte`/`u64`/`pubkey`); blob support is Option B.

Strategy: every field's canonical witness is `singletonMemBytes (base+off)
fv.bytes` (uniform), so the `**` chain's split is a fold of byte-blobs.
Disjointness reduces to one range lemma + the existing `Disjoint_union_of_both`;
the satisfaction side is `fv.coarse = ↦Bytes fv.bytes`; compatibility rewrites
each block back to its native singleton and reuses the per-atom builders. -/

/-- Canonical LE byte encoding a field's coarse atom owns (right-associated so the
    pubkey blob peels cleanly under `singletonMemBytes_union_adj`). -/
def FieldVal.bytes : FieldVal → ByteArray
  | .byte v    => byteBA v
  | .u64 v     => u64LE v
  | .pubkey p  => u64LE p.c0 ++ (u64LE p.c1 ++ (u64LE p.c2 ++ u64LE p.c3))
  | .blob segs => segsBytes segs

/-- Byte width of a field. -/
def FieldVal.width : FieldVal → Nat
  | .byte _    => 1
  | .u64 _     => 8
  | .pubkey _  => 32
  | .blob segs => (segsBytes segs).size

theorem FieldVal.bytes_size (fv : FieldVal) : fv.bytes.size = fv.width := by
  cases fv <;> simp [FieldVal.bytes, FieldVal.width, u64LE_size, byteBA_size]

/-- Byte fields must be canonical (`< 256`) for the `↦ₘ`↔`↦Bytes` bridge. -/
def FieldVal.byteWF : FieldVal → Prop
  | .byte v => v < 256
  | _       => True

/-- The per-field read hypotheses `encodeState` supplies. Scalars decode to a
    `readU*`/`pubkeyAt`; an opaque blob is a byte-range equality (the bytes are
    in memory) — there is no scalar read for an un-decoded region. -/
def fieldRead (s : State) (addr : Nat) : FieldVal → Prop
  | .byte v    => readU8 s.mem addr = v
  | .u64 v     => readU64 s.mem addr = v % 2 ^ 64
  | .pubkey p  => pubkeyAt s.mem addr p
  | .blob segs => ∀ i, i < (segsBytes segs).size →
                    s.mem (addr + i) = ((segsBytes segs).get! i).toNat

/-- Build a union's `CompatibleWith` from both halves (left-biased union, no
    disjointness needed: whichever side owns a cell agrees with `s`). -/
theorem compatibleWith_union_of {h1 h2 : PartialState} {s : State}
    (c1 : h1.CompatibleWith s) (c2 : h2.CompatibleWith s) :
    (h1.union h2).CompatibleWith s where
  regs := fun r v hr => by
    rcases hx : h1.regs r with _ | v1
    · rw [union_regs_of_left_none hx] at hr; exact c2.regs r v hr
    · rw [union_regs_of_left_some hx] at hr; injection hr with e; exact e ▸ c1.regs r v1 hx
  mem := fun a v hr => by
    rcases hx : h1.mem a with _ | v1
    · rw [union_mem_of_left_none hx] at hr; exact c2.mem a v hr
    · rw [union_mem_of_left_some hx] at hr; injection hr with e; exact e ▸ c1.mem a v1 hx
  pc := fun v hr => by
    rcases hx : h1.pc with _ | v1
    · rw [union_pc_of_left_none hx] at hr; exact c2.pc v hr
    · rw [union_pc_of_left_some hx] at hr; injection hr with e; exact e ▸ c1.pc v1 hx
  returnData := fun rd hr => by
    rcases hx : h1.returnData with _ | v1
    · rw [union_returnData_of_left_none hx] at hr; exact c2.returnData rd hr
    · rw [union_returnData_of_left_some hx] at hr; injection hr with e; exact e ▸ c1.returnData v1 hx
  callStack := fun cs hr => by
    rcases hx : h1.callStack with _ | v1
    · rw [union_callStack_of_left_none hx] at hr; exact c2.callStack cs hr
    · rw [union_callStack_of_left_some hx] at hr; injection hr with e; exact e ▸ c1.callStack v1 hx

/-- Two byte blobs at non-overlapping ranges own disjoint memory (general
    sibling of `singletonMemBytes_disjoint_adj`). -/
theorem singletonMemBytes_disjoint_of_ranges {a1 a2 : Nat} {bs1 bs2 : ByteArray}
    (h : a1 + bs1.size ≤ a2 ∨ a2 + bs2.size ≤ a1) :
    (singletonMemBytes a1 bs1).Disjoint (singletonMemBytes a2 bs2) where
  regs := fun _ => Or.inl rfl
  mem := fun a => by
    by_cases hin : a1 ≤ a ∧ a < a1 + bs1.size
    · right; exact singletonMemBytes_mem_outside a2 bs2 a (by omega)
    · left; exact singletonMemBytes_mem_outside a1 bs1 a (by omega)
  pc := Or.inl rfl
  returnData := Or.inl rfl
  callStack := Or.inl rfl

/-- Build `CompatibleWith` for a byte-blob from its per-byte values (the blob /
    Option-B compatibility primitive). -/
theorem compatibleWith_singletonMemBytes {addr : Nat} {bs : ByteArray} {s : State}
    (h : ∀ i, i < bs.size → s.mem (addr + i) = (bs.get! i).toNat) :
    (singletonMemBytes addr bs).CompatibleWith s where
  regs := fun _ _ hr => by simp at hr
  mem := fun a' v' ha' => by
    by_cases hin : addr ≤ a' ∧ a' < addr + bs.size
    · obtain ⟨hlo, hhi⟩ := hin
      have hidx : a' - addr < bs.size := by omega
      have heq : addr + (a' - addr) = a' := by omega
      have key := singletonMemBytes_mem_at addr bs (a' - addr) hidx
      rw [heq] at key
      rw [key] at ha'
      injection ha' with e
      rw [← e]
      have := h (a' - addr) hidx
      rw [heq] at this
      exact this
    · rw [singletonMemBytes_mem_outside addr bs a' (by omega)] at ha'; simp at ha'
  pc := fun _ hr => by simp at hr
  returnData := fun _ hr => by simp at hr
  callStack := fun _ hr => by simp at hr

/-- Empty owns nothing, so it is compatible with any state. -/
theorem compatibleWith_empty {s : State} : PartialState.empty.CompatibleWith s where
  regs := fun _ _ h => by simp at h
  mem := fun _ _ h => by simp at h
  pc := fun _ h => by simp at h
  returnData := fun _ h => by simp at h
  callStack := fun _ h => by simp at h

/-- Assertion-level form of `memBytesIs_append` (for `rw` under `**`). -/
theorem memBytesIs_append_eq (addr : Nat) (bs1 bs2 : ByteArray) :
    memBytesIs addr (bs1 ++ bs2) = (memBytesIs addr bs1 ** memBytesIs (addr + bs1.size) bs2) :=
  funext fun h => propext (memBytesIs_append addr bs1 bs2 h)

/-- Assertion-level form of `memU64Is_eq_memBytesIs`. -/
theorem memU64Is_eq_bytes_eq (a v : Nat) : memU64Is a v = memBytesIs a (u64LE v) :=
  funext fun h => propext (memU64Is_eq_memBytesIs a v h)

/-- A pubkey atom is the byte-blob of its four LE limbs. -/
theorem pubkeyIs_eq_bytes (addr : Nat) (p : Pubkey) :
    pubkeyIs addr p
      = memBytesIs addr (u64LE p.c0 ++ (u64LE p.c1 ++ (u64LE p.c2 ++ u64LE p.c3))) := by
  simp only [pubkeyIs]
  rw [memBytesIs_append_eq addr (u64LE p.c0), u64LE_size,
      memBytesIs_append_eq (addr + 8) (u64LE p.c1), u64LE_size,
      memBytesIs_append_eq (addr + 8 + 8) (u64LE p.c2) (u64LE p.c3), u64LE_size,
      show addr + 8 + 8 = addr + 16 from by omega,
      show addr + 16 + 8 = addr + 24 from by omega,
      ← memU64Is_eq_bytes_eq addr p.c0, ← memU64Is_eq_bytes_eq (addr + 8) p.c1,
      ← memU64Is_eq_bytes_eq (addr + 16) p.c2, ← memU64Is_eq_bytes_eq (addr + 24) p.c3]

/-- A scalar field's coarse atom holds on its canonical byte-blob witness. -/
theorem fieldCoarse_on_bytes (addr : Nat) (fv : FieldVal) (hwf : fv.byteWF) :
    (fv.coarse addr) (singletonMemBytes addr fv.bytes) := by
  cases fv with
  | byte v =>
    exact (memByteIs_eq_memBytesIs addr v hwf (singletonMemBytes addr (byteBA v))).mpr rfl
  | u64 v =>
    exact (memU64Is_eq_memBytesIs addr v (singletonMemBytes addr (u64LE v))).mpr rfl
  | pubkey p =>
    show pubkeyIs addr p
      (singletonMemBytes addr (u64LE p.c0 ++ (u64LE p.c1 ++ (u64LE p.c2 ++ u64LE p.c3))))
    rw [pubkeyIs_eq_bytes addr p]; rfl
  | blob segs => exact rfl

/-- A field's canonical byte-blob witness is compatible with `s`, given the field
    read and byte canonicality. -/
theorem fieldCompat (addr : Nat) (fv : FieldVal)
    (hc : ∀ x, s.mem x < 256) (hr : fieldRead s addr fv) :
    (singletonMemBytes addr fv.bytes).CompatibleWith s := by
  cases fv with
  | byte v =>
    simp only [fieldRead, readU8] at hr
    have hb := hc addr
    rw [show (FieldVal.byte v).bytes = byteBA v from rfl, ← singletonMem_eq_bytes addr v (by omega)]
    exact compatibleWith_singletonMem (by omega)
  | u64 v =>
    rw [show (FieldVal.u64 v).bytes = u64LE v from rfl, ← singletonMemU64_eq_bytes]
    have c0 := hc addr; have c1 := hc (addr + 1); have c2 := hc (addr + 2)
    have c3 := hc (addr + 3); have c4 := hc (addr + 4); have c5 := hc (addr + 5)
    have c6 := hc (addr + 6); have c7 := hc (addr + 7)
    simp only [fieldRead, readU64] at hr
    exact compatibleWith_singletonMemU64 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  | pubkey p =>
    simp only [fieldRead, pubkeyAt] at hr
    obtain ⟨r0, r1, r2, r3⟩ := hr
    show (singletonMemBytes addr (u64LE p.c0 ++ (u64LE p.c1 ++ (u64LE p.c2 ++ u64LE p.c3)))).CompatibleWith s
    rw [← singletonMemBytes_union_adj addr (u64LE p.c0) _, u64LE_size,
        ← singletonMemBytes_union_adj (addr + 8) (u64LE p.c1) _, u64LE_size,
        ← singletonMemBytes_union_adj (addr + 8 + 8) (u64LE p.c2) (u64LE p.c3), u64LE_size]
    rw [show addr + 8 + 8 = addr + 16 from by omega, show addr + 16 + 8 = addr + 24 from by omega]
    rw [← singletonMemU64_eq_bytes, ← singletonMemU64_eq_bytes,
        ← singletonMemU64_eq_bytes, ← singletonMemU64_eq_bytes]
    refine compatibleWith_union_of ?_ (compatibleWith_union_of ?_ (compatibleWith_union_of ?_ ?_))
    · have c0 := hc addr; have c1 := hc (addr+1); have c2 := hc (addr+2); have c3 := hc (addr+3)
      have c4 := hc (addr+4); have c5 := hc (addr+5); have c6 := hc (addr+6); have c7 := hc (addr+7)
      simp only [readU64] at r0
      exact compatibleWith_singletonMemU64 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · have c0 := hc (addr+8); have c1 := hc (addr+8+1); have c2 := hc (addr+8+2); have c3 := hc (addr+8+3)
      have c4 := hc (addr+8+4); have c5 := hc (addr+8+5); have c6 := hc (addr+8+6); have c7 := hc (addr+8+7)
      simp only [readU64] at r1
      exact compatibleWith_singletonMemU64 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · have c0 := hc (addr+16); have c1 := hc (addr+16+1); have c2 := hc (addr+16+2); have c3 := hc (addr+16+3)
      have c4 := hc (addr+16+4); have c5 := hc (addr+16+5); have c6 := hc (addr+16+6); have c7 := hc (addr+16+7)
      simp only [readU64] at r2
      exact compatibleWith_singletonMemU64 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · have c0 := hc (addr+24); have c1 := hc (addr+24+1); have c2 := hc (addr+24+2); have c3 := hc (addr+24+3)
      have c4 := hc (addr+24+4); have c5 := hc (addr+24+5); have c6 := hc (addr+24+6); have c7 := hc (addr+24+7)
      simp only [readU64] at r3
      exact compatibleWith_singletonMemU64 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  | blob segs =>
    simp only [fieldRead] at hr
    exact compatibleWith_singletonMemBytes hr

/-- Pairwise offset-non-overlap of a layout (a separate predicate — `codecValid`
    deliberately does not carry this). -/
def layoutDisjoint : List (Nat × FieldVal) → Prop
  | [] => True
  | (off, fv) :: rest =>
      (∀ p ∈ rest, off + fv.width ≤ p.1 ∨ p.1 + p.2.width ≤ off) ∧ layoutDisjoint rest

/-- The canonical witness partial state for a layout: a fold of byte-blobs. -/
def codecState (base : Nat) : List (Nat × FieldVal) → PartialState
  | [] => PartialState.empty
  | (off, fv) :: rest =>
      (singletonMemBytes (base + off) fv.bytes).union (codecState base rest)

/-- The head byte-blob is disjoint from the rest of the layout's witness. -/
theorem singletonMemBytes_disjoint_codecState {base off : Nat} {fv : FieldVal}
    {rest : List (Nat × FieldVal)}
    (h : ∀ p ∈ rest, off + fv.width ≤ p.1 ∨ p.1 + p.2.width ≤ off) :
    (singletonMemBytes (base + off) fv.bytes).Disjoint (codecState base rest) := by
  induction rest with
  | nil => exact Disjoint_empty_right
  | cons hd tl ih =>
    obtain ⟨o2, f2⟩ := hd
    show (singletonMemBytes (base + off) fv.bytes).Disjoint
      ((singletonMemBytes (base + o2) f2.bytes).union (codecState base tl))
    have hhead : off + fv.width ≤ o2 ∨ o2 + f2.width ≤ off := h (o2, f2) ((List.mem_cons.2 (Or.inl rfl)))
    have d1 : (singletonMemBytes (base + off) fv.bytes).Disjoint
        (singletonMemBytes (base + o2) f2.bytes) :=
      singletonMemBytes_disjoint_of_ranges (by
        rw [fv.bytes_size, f2.bytes_size]; omega)
    have d2 : (singletonMemBytes (base + off) fv.bytes).Disjoint (codecState base tl) :=
      ih (fun p hp => h p ((List.mem_cons.2 (Or.inr hp))))
    exact (Disjoint_union_of_both d1.symm d2.symm).symm

/-- The canonical witness satisfies the coarse codec (the `**` split is the fold),
    given byte-WF fields and a non-overlapping layout. -/
theorem codecState_sat {base : Nat} :
    ∀ (fields : List (Nat × FieldVal)),
      (∀ p ∈ fields, p.2.byteWF) → layoutDisjoint fields →
      (codecCoarse base fields) (codecState base fields) := by
  intro fields
  induction fields with
  | nil => intro _ _; exact rfl
  | cons hd rest ih =>
    obtain ⟨off, fv⟩ := hd
    intro hwf hdisj
    obtain ⟨hd_disj, hrest_disj⟩ := hdisj
    refine ⟨singletonMemBytes (base + off) fv.bytes, codecState base rest, ?_, rfl, ?_, ?_⟩
    · exact singletonMemBytes_disjoint_codecState hd_disj
    · exact fieldCoarse_on_bytes (base + off) fv (hwf (off, fv) ((List.mem_cons.2 (Or.inl rfl))))
    · exact ih (fun p hp => hwf p ((List.mem_cons.2 (Or.inr hp)))) hrest_disj

/-- The canonical witness is compatible with `s`, given per-field reads. -/
theorem codecState_compat {base : Nat} {s : State} (hc : ∀ x, s.mem x < 256) :
    ∀ (fields : List (Nat × FieldVal)),
      (∀ p ∈ fields, fieldRead s (base + p.1) p.2) →
      (codecState base fields).CompatibleWith s := by
  intro fields
  induction fields with
  | nil => intro _; exact compatibleWith_empty
  | cons hd rest ih =>
    obtain ⟨off, fv⟩ := hd
    intro hr
    refine compatibleWith_union_of ?_ ?_
    · exact fieldCompat (base + off) fv hc (hr (off, fv) ((List.mem_cons.2 (Or.inl rfl))))
    · exact ih (fun p hp => hr p ((List.mem_cons.2 (Or.inr hp))))

/-- **Reverse codec reassembly (Option B).** Given the per-field reads, byte
    canonicality, byte-WF, and a non-overlapping layout, rebuild
    `holdsFor (codecCoarse base fields) s` — the "build the pre from `encodeState`"
    direction of the discharge bridge.  Handles any field kind, incl. opaque
    blobs (whose `fieldRead` is the byte-range equality). -/
theorem holdsFor_codecCoarse_of_reads {base : Nat} {s : State}
    {fields : List (Nat × FieldVal)}
    (hc : ∀ x, s.mem x < 256)
    (hwf : ∀ p ∈ fields, p.2.byteWF)
    (hdisj : layoutDisjoint fields)
    (hr : ∀ p ∈ fields, fieldRead s (base + p.1) p.2) :
    (codecCoarse base fields).holdsFor s :=
  ⟨codecState base fields, codecState_compat hc fields hr, codecState_sat fields hwf hdisj⟩

/-- `StateBounded` wrapper for the reverse codec reassembly. -/
theorem holdsFor_codecCoarse_of_reads_bounded {base : Nat} {s : State}
    {fields : List (Nat × FieldVal)}
    (hb : StateBounded s)
    (hwf : ∀ p ∈ fields, p.2.byteWF)
    (hdisj : layoutDisjoint fields)
    (hr : ∀ p ∈ fields, fieldRead s (base + p.1) p.2) :
    (codecCoarse base fields).holdsFor s :=
  holdsFor_codecCoarse_of_reads hb.mem_lt hwf hdisj hr

/-! ## Validation — the bridges compose

Forward then reverse round-trips the atom through its read form, and the codec
decomposition composes with a per-atom forward bridge to extract a per-field
read straight out of a coarse codec (the `encodeState`-recovery shape). -/

-- Forward ∘ reverse recovers the `↦U64` atom (round-trip via the read form).
example {a v : Nat} {s : State} (hc : ∀ x, s.mem x < 256)
    (h : (memU64Is a v).holdsFor s) : (memU64Is a v).holdsFor s :=
  holdsFor_memU64Is_of_read hc (readU64_of_holdsFor_memU64Is h)

-- A coarse codec exposes a per-field U64 read, layout-generally.
example {base amount : Nat} {s : State}
    (h : (codecCoarse base [(64, FieldVal.u64 amount)]).holdsFor s) :
    readU64 s.mem (base + 64) = amount % 2 ^ 64 := by
  have hf : ((FieldVal.u64 amount).coarse (base + 64)).holdsFor s :=
    holdsFor_codecCoarse_field _ h (by simp)
  exact readU64_of_holdsFor_memU64Is hf

-- Reverse: per-field reads + canonicality + non-overlap rebuild the codec
-- `holdsFor` — a single-`u64` layout.
example {base amount : Nat} {s : State} (hc : ∀ x, s.mem x < 256)
    (hr : readU64 s.mem (base + 64) = amount % 2 ^ 64) :
    (codecCoarse base [(64, FieldVal.u64 amount)]).holdsFor s := by
  refine holdsFor_codecCoarse_of_reads hc ?_ ?_ ?_
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp; trivial
  · simp [layoutDisjoint]
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hr

-- Reverse with a pubkey field (exercises the 4-limb path) + a u64, with a
-- genuine inter-field non-overlap obligation.
example {base amount : Nat} {owner : Pubkey} {s : State} (hc : ∀ x, s.mem x < 256)
    (h0 : pubkeyAt s.mem (base + 0) owner)
    (h1 : readU64 s.mem (base + 32) = amount % 2 ^ 64) :
    (codecCoarse base [(0, FieldVal.pubkey owner), (32, FieldVal.u64 amount)]).holdsFor s := by
  refine holdsFor_codecCoarse_of_reads hc ?_ ?_ ?_
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · trivial
    · rcases List.mem_cons.mp hp with rfl | hp
      · trivial
      · simp at hp
  · refine ⟨?_, by simp [layoutDisjoint]⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · left; simp [FieldVal.width]
    · simp at hp
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h0
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact h1
      · simp at hp

-- Reverse (Option B): an opaque blob field rebuilds from its byte-range read.
example {base : Nat} {segs : List FieldSeg} {s : State} (hc : ∀ x, s.mem x < 256)
    (hr : ∀ i, i < (segsBytes segs).size →
            s.mem (base + 0 + i) = ((segsBytes segs).get! i).toNat) :
    (codecCoarse base [(0, FieldVal.blob segs)]).holdsFor s := by
  refine holdsFor_codecCoarse_of_reads hc ?_ ?_ ?_
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp; trivial
  · simp [layoutDisjoint]
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hr

end SVM.SBPF
