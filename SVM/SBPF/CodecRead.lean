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
  needs an offset-non-overlap predicate to reassemble the `**` witness; that
  piece is deferred (see issue #48). This file delivers the load-bearing
  per-atom bridges both ways, plus the forward codec decomposition.
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

end SVM.SBPF
