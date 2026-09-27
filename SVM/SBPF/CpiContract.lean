/-
  CPI contracts in separation-logic form, for composing a caller's path
  across an invoke (the suffix after `Cpi.cuTripleWithinMem_cpi_bridge`).

  `cpiTriple callee Pc Qc`: from any state owning `Pc` framed by `R`, every
  result the callee contract admits lands in `Qc r ** R` after
  `Cpi.applyResult`. `applyResult` rewrites r0 and the return-data buffer, so
  `Pc` must own both; on success it installs the callee's proposed memory, so
  preserving `R`'s memory is the contract's obligation.

  `cpiTriple_of_mem_preserving` discharges the triple for callees that never
  change caller memory (zero-account or read-only CPIs): the result's code
  lands in r0 and its return data in the owned buffer, everything else framed.
-/

import SVM.SBPF.CpiBridge

namespace SVM.SBPF

namespace PartialState

/-- The right half of a compatible disjoint union is itself compatible. -/
theorem CompatibleWith.of_union_right {h1 h2 hp : PartialState} {s : State}
    (hc : hp.CompatibleWith s) (hu : h1.union h2 = hp) (hd : h1.Disjoint h2) :
    h2.CompatibleWith s where
  regs r v h := by
    rcases hd.regs r with hn | hn
    · exact hc.regs r v (by rw [← hu, union_regs_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  mem a v h := by
    rcases hd.mem a with hn | hn
    · exact hc.mem a v (by rw [← hu, union_mem_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  pc v h := by
    rcases hd.pc with hn | hn
    · exact hc.pc v (by rw [← hu, union_pc_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  returnData rd h := by
    rcases hd.returnData with hn | hn
    · exact hc.returnData rd (by rw [← hu, union_returnData_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  callStack cs h := by
    rcases hd.callStack with hn | hn
    · exact hc.callStack cs (by rw [← hu, union_callStack_of_left_none hn]; exact h)
    · rw [hn] at h; cases h

end PartialState

namespace Cpi

open PartialState

/-- Separation-logic CPI contract: `Pc ** R` before the invoke, `Qc r ** R`
    after `applyResult` for every result `r` the callee admits. -/
def cpiTriple (callee : CalleeSemantics) (Pc : Assertion)
    (Qc : CalleeResult → Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (s : State) (r : CalleeResult),
    (Pc ** R).holdsFor s → callee s r → (Qc r ** R).holdsFor (applyResult s r)

/-- The owned r0 + return-data footprint as a partial state. -/
private def r0RdState (v : Nat) (rd : ByteArray) : PartialState :=
  (singletonReg .r0 v).union (singletonReturnData rd)

private theorem r0Rd_disjoint (v : Nat) (rd : ByteArray) :
    (singletonReg .r0 v).Disjoint (singletonReturnData rd) where
  regs _ := Or.inr (singletonReturnData_regs _)
  mem _ := Or.inl (singletonReg_mem _)
  pc := Or.inl singletonReg_pc
  returnData := Or.inl singletonReg_returnData
  callStack := Or.inl singletonReg_callStack

private theorem r0Rd_sat (v : Nat) (rd : ByteArray) :
    ((.r0 ↦ᵣ v) ** returnDataIs rd) (r0RdState v rd) :=
  ⟨_, _, r0Rd_disjoint v rd, rfl, rfl, rfl⟩

private theorem r0Rd_regs_r0 (v : Nat) (rd : ByteArray) :
    (r0RdState v rd).regs .r0 = some v :=
  union_regs_of_left_some singletonReg_regs_self

private theorem r0Rd_regs_other (v : Nat) (rd : ByteArray) {reg : Reg} (h : reg ≠ .r0) :
    (r0RdState v rd).regs reg = none := by
  unfold r0RdState
  rw [union_regs_of_left_none (singletonReg_regs_other h)]
  exact singletonReturnData_regs _

private theorem r0Rd_returnData (v : Nat) (rd : ByteArray) :
    (r0RdState v rd).returnData = some rd := by
  unfold r0RdState
  rw [union_returnData_of_left_none singletonReg_returnData]
  exact singletonReturnData_returnData_self

/-- A callee that never changes caller memory satisfies the r0/return-data
    CPI triple: the result code lands in r0 and its return data in the owned
    buffer; every framed register, memory cell and the call stack survive. -/
theorem cpiTriple_of_mem_preserving (callee : CalleeSemantics) (v : Nat) (rd : ByteArray)
    (hMem : ∀ s r, callee s r → r.mem = s.mem) :
    cpiTriple callee ((.r0 ↦ᵣ v) ** returnDataIs rd)
      (fun r => (.r0 ↦ᵣ r.code) ** returnDataIs r.returnData) := by
  intro R hR s r hPre hCallee
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hPc, hRh2⟩ := hPre
  obtain ⟨a, b, _, huab, ha, hb⟩ := hPc
  subst ha hb
  have h1Eq : h1 = r0RdState v rd := huab.symm
  subst h1Eq
  have h2r0 : h2.regs .r0 = none :=
    (hd12.regs .r0).resolve_left (by rw [r0Rd_regs_r0]; simp)
  have h2rd : h2.returnData = none :=
    hd12.returnData.resolve_left (by rw [r0Rd_returnData]; simp)
  have h2pc : h2.pc = none := hR h2 hRh2
  have hc2 : h2.CompatibleWith s := CompatibleWith.of_union_right hcompat hu12 hd12
  have hMemEq : (applyResult s r).mem = s.mem := by
    by_cases hc : r.code = 0
    · rw [applyResult_mem_success s r hc, hMem s r hCallee]
    · exact applyResult_mem_failure s r hc
  let h1' := r0RdState r.code r.returnData
  have hd' : h1'.Disjoint h2 :=
    { regs := fun reg => by
        by_cases hreg : reg = .r0
        · subst hreg; exact Or.inr h2r0
        · exact Or.inl (r0Rd_regs_other _ _ hreg)
      mem := fun _ => Or.inl (by simp [h1', r0RdState, union_mem_of_left_none])
      pc := Or.inl (by simp [h1', r0RdState, union_pc_of_left_none])
      returnData := Or.inr h2rd
      callStack := Or.inl (by simp [h1', r0RdState]) }
  refine ⟨h1'.union h2, ?_, h1', h2, hd', rfl, r0Rd_sat _ _, hRh2⟩
  refine
    { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
  · intro reg val hval
    by_cases hreg : reg = .r0
    · subst hreg
      rw [union_regs_of_left_some (r0Rd_regs_r0 _ _)] at hval
      cases hval
      rfl
    · rw [union_regs_of_left_none (r0Rd_regs_other _ _ hreg)] at hval
      rw [← hc2.regs reg val hval]
      cases reg <;> first | exact absurd rfl hreg | rfl
  · intro addr val hval
    rw [union_mem_of_left_none (by simp [h1', r0RdState, union_mem_of_left_none])] at hval
    rw [hMemEq]
    exact hc2.mem addr val hval
  · intro val hval
    rw [union_pc_of_left_none (by simp [h1', r0RdState, union_pc_of_left_none]), h2pc] at hval
    cases hval
  · intro val hval
    rw [union_returnData_of_left_some (r0Rd_returnData _ _)] at hval
    cases hval
    rfl
  · intro cs hval
    rw [union_callStack_of_left_none (by simp [h1', r0RdState])] at hval
    exact hc2.callStack cs hval

/-! ## Account-writing callees

A callee that writes caller memory (account data write-back) is described by
the byte addresses it may change. The contract owns exactly those bytes as
`↦ₘ` cells; afterwards each holds `committedByte r a old`: the callee's
proposed byte on success, the caller's own byte on rollback. -/

/-- The callee changes caller memory only at the listed byte addresses. -/
def writesOnly (callee : CalleeSemantics) (addrs : List Nat) : Prop :=
  ∀ s r, callee s r → ∀ a, a ∉ addrs → r.mem a = s.mem a

/-- A footprint byte after the CPI: proposed on success, rolled back otherwise. -/
def committedByte (r : CalleeResult) (a old : Nat) : Nat :=
  if r.code = 0 then r.mem a else old

/-- Separating conjunction of byte cells, without a trailing `emp` so it
    unfolds to plain `↦ₘ` atoms for a concrete list. -/
def bytesAt : List (Nat × Nat) → Assertion
  | [] => emp
  | [(a, v)] => (a ↦ₘ v)
  | (a, v) :: b :: rest => (a ↦ₘ v) ** bytesAt (b :: rest)

/-- Every footprint cell after the CPI. -/
def commitCells (r : CalleeResult) (cells : List (Nat × Nat)) : List (Nat × Nat) :=
  cells.map fun c => (c.1, committedByte r c.1 c.2)

/-- The partial state owning exactly `cells`. -/
def cellsState (cells : List (Nat × Nat)) : PartialState :=
  { regs := fun _ => none, mem := fun a => cells.lookup a, pc := none }

private theorem lookup_eq_none_of_not_mem {a : Nat} :
    ∀ {t : List (Nat × Nat)}, a ∉ t.map Prod.fst → t.lookup a = none
  | [], _ => rfl
  | (b, w) :: t, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup_cons]
    rw [show (a == b) = false from beq_false_of_ne h.1]
    exact lookup_eq_none_of_not_mem h.2

private theorem lookup_isSome_of_mem {a : Nat} :
    ∀ {t : List (Nat × Nat)}, a ∈ t.map Prod.fst → ∃ w, t.lookup a = some w
  | [], h => by simp at h
  | (b, w) :: t, h => by
    simp only [List.lookup_cons]
    by_cases hab : a = b
    · subst hab; exact ⟨w, by simp⟩
    · rw [show (a == b) = false from beq_false_of_ne hab]
      simp only [List.map_cons, List.mem_cons, hab, false_or] at h
      exact lookup_isSome_of_mem h

private theorem cellsState_single (a v : Nat) :
    cellsState [(a, v)] = singletonMem a v := by
  simp only [cellsState, singletonMem, PartialState.mk.injEq, true_and, and_true]
  funext a'
  by_cases h : a' = a
  · subst h; simp
  · simp only [List.lookup_cons, List.lookup_nil, h, if_false]
    rw [show (a' == a) = false from beq_false_of_ne h]

private theorem cellsState_cons (a v : Nat) (t : List (Nat × Nat)) :
    (singletonMem a v).union (cellsState t) = cellsState ((a, v) :: t) := by
  simp only [PartialState.union, cellsState, singletonMem, PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · first | rfl | trivial
  · funext a'
    by_cases h : a' = a
    · subst h; simp
    · simp only [h, if_false, List.lookup_cons]
      rw [show (a' == a) = false from beq_false_of_ne h]
  all_goals first | rfl | trivial

private theorem singletonMem_disjoint_cells {a v : Nat} {t : List (Nat × Nat)}
    (h : a ∉ t.map Prod.fst) : (singletonMem a v).Disjoint (cellsState t) where
  regs _ := Or.inl rfl
  mem a' := by
    by_cases ha : a' = a
    · subst ha; exact Or.inr (lookup_eq_none_of_not_mem h)
    · exact Or.inl (singletonMem_mem_other ha)
  pc := Or.inl rfl
  returnData := Or.inl rfl
  callStack := Or.inl rfl

theorem bytesAt_iff :
    ∀ (cells : List (Nat × Nat)) (h : PartialState),
      bytesAt cells h ↔ ((cells.map Prod.fst).Nodup ∧ h = cellsState cells)
  | [], h => by
    simp only [bytesAt, emp, List.map_nil, List.nodup_nil, true_and]
    constructor <;> intro hh <;> rw [hh] <;> rfl
  | [(a, v)], h => by
    simp only [bytesAt, memByteIs, List.map_cons, List.map_nil, List.nodup_cons,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, true_and,
      cellsState_single]
  | (a, v) :: b :: rest, h => by
    have ih := bytesAt_iff (b :: rest)
    constructor
    · rintro ⟨h1, h2, hd, hu, h1eq, h2sat⟩
      obtain ⟨hnd, h2eq⟩ := (ih h2).mp h2sat
      subst h1eq h2eq
      refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩, ?_⟩
      · obtain ⟨w, hw⟩ := lookup_isSome_of_mem hmem
        rcases hd.mem a with hn | hn
        · simp at hn
        · simp only [cellsState] at hn
          rw [hn] at hw; cases hw
      · rw [← hu, cellsState_cons]
    · rintro ⟨hnd, rfl⟩
      obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
      exact ⟨singletonMem a v, cellsState (b :: rest),
        singletonMem_disjoint_cells hnotin, cellsState_cons a v (b :: rest), rfl,
        (ih _).mpr ⟨hnd', rfl⟩⟩

theorem commitCells_keys (r : CalleeResult) (cells : List (Nat × Nat)) :
    (commitCells r cells).map Prod.fst = cells.map Prod.fst := by
  simp [commitCells, Function.comp_def]

private theorem lookup_commitCells (r : CalleeResult) (a : Nat) :
    ∀ cells : List (Nat × Nat),
      (commitCells r cells).lookup a = (cells.lookup a).map (committedByte r a)
  | [] => rfl
  | (b, w) :: t => by
    simp only [commitCells, List.map_cons, List.lookup_cons]
    by_cases hab : a = b
    · subst hab; simp
    · rw [show (a == b) = false from beq_false_of_ne hab]
      exact lookup_commitCells r a t

/-- The left half of a compatible union is compatible (unions are left-biased). -/
theorem CompatibleWith.of_union_left {h1 h2 hp : PartialState} {s : State}
    (hc : hp.CompatibleWith s) (hu : h1.union h2 = hp) : h1.CompatibleWith s where
  regs r v h := hc.regs r v (by rw [← hu]; exact union_regs_of_left_some h)
  mem a v h := hc.mem a v (by rw [← hu]; exact union_mem_of_left_some h)
  pc v h := hc.pc v (by rw [← hu]; exact union_pc_of_left_some h)
  returnData rd h := hc.returnData rd (by rw [← hu]; exact union_returnData_of_left_some h)
  callStack cs h := hc.callStack cs (by rw [← hu]; exact union_callStack_of_left_some h)

/-- Any two compatible partial states have a compatible union. -/
theorem compat_union {h1 h2 : PartialState} {s : State}
    (c1 : h1.CompatibleWith s) (c2 : h2.CompatibleWith s) : (h1.union h2).CompatibleWith s where
  regs r v h := by
    cases e : h1.regs r with
    | some w => rw [union_regs_of_left_some e] at h; obtain rfl := Option.some.inj h; exact c1.regs r _ e
    | none => rw [union_regs_of_left_none e] at h; exact c2.regs r v h
  mem a v h := by
    cases e : h1.mem a with
    | some w => rw [union_mem_of_left_some e] at h; obtain rfl := Option.some.inj h; exact c1.mem a _ e
    | none => rw [union_mem_of_left_none e] at h; exact c2.mem a v h
  pc v h := by
    cases e : h1.pc with
    | some w => rw [union_pc_of_left_some e] at h; obtain rfl := Option.some.inj h; exact c1.pc _ e
    | none => rw [union_pc_of_left_none e] at h; exact c2.pc v h
  returnData rd h := by
    cases e : h1.returnData with
    | some w => rw [union_returnData_of_left_some e] at h; obtain rfl := Option.some.inj h; exact c1.returnData _ e
    | none => rw [union_returnData_of_left_none e] at h; exact c2.returnData rd h
  callStack cs h := by
    cases e : h1.callStack with
    | some w => rw [union_callStack_of_left_some e] at h; obtain rfl := Option.some.inj h; exact c1.callStack _ e
    | none => rw [union_callStack_of_left_none e] at h; exact c2.callStack cs h

/-- The footprint partial state: r0, the return-data buffer and the cells. -/
def fpState (v : Nat) (rd : ByteArray) (cells : List (Nat × Nat)) : PartialState :=
  (singletonReg .r0 v).union ((singletonReturnData rd).union (cellsState cells))

@[simp] theorem fpState_regs (v : Nat) (rd : ByteArray) (cells : List (Nat × Nat)) (reg : Reg) :
    (fpState v rd cells).regs reg = if reg = .r0 then some v else none := by
  cases reg <;> rfl

@[simp] theorem fpState_mem (v : Nat) (rd : ByteArray) (cells : List (Nat × Nat)) (a : Nat) :
    (fpState v rd cells).mem a = cells.lookup a := rfl

@[simp] theorem fpState_pc (v : Nat) (rd : ByteArray) (cells : List (Nat × Nat)) :
    (fpState v rd cells).pc = none := rfl

@[simp] theorem fpState_returnData (v : Nat) (rd : ByteArray) (cells : List (Nat × Nat)) :
    (fpState v rd cells).returnData = some rd := rfl

@[simp] theorem fpState_callStack (v : Nat) (rd : ByteArray) (cells : List (Nat × Nat)) :
    (fpState v rd cells).callStack = none := rfl

theorem fpState_iff (v : Nat) (rd : ByteArray) (cells : List (Nat × Nat)) (h : PartialState) :
    ((.r0 ↦ᵣ v) ** returnDataIs rd ** bytesAt cells) h ↔
      ((cells.map Prod.fst).Nodup ∧ h = fpState v rd cells) := by
  constructor
  · rintro ⟨h0, hrest, _, hu0, h0eq, hr0, hc, _, hurc, hrdeq, hcSat⟩
    obtain ⟨hnd, hceq⟩ := (bytesAt_iff cells hc).mp hcSat
    subst h0eq hrdeq hceq
    exact ⟨hnd, by rw [← hu0, ← hurc]; rfl⟩
  · rintro ⟨hnd, rfl⟩
    refine ⟨singletonReg .r0 v, (singletonReturnData rd).union (cellsState cells), ?_, rfl,
      rfl, singletonReturnData rd, cellsState cells, ?_, rfl, rfl,
      (bytesAt_iff cells _).mpr ⟨hnd, rfl⟩⟩
    · exact { regs := fun r => by cases r <;> simp [PartialState.union, cellsState, singletonReg,
                  singletonReturnData]
              mem := fun _ => Or.inl rfl, pc := Or.inl rfl, returnData := Or.inl rfl,
              callStack := Or.inl rfl }
    · exact { regs := fun _ => Or.inl rfl, mem := fun _ => Or.inl rfl, pc := Or.inl rfl,
              returnData := Or.inr rfl, callStack := Or.inl rfl }

/-- An account-writing callee satisfies the footprint CPI triple: r0 takes the
    result code, the return-data buffer the callee's, each footprint byte its
    `committedByte`, and every framed resource survives (the callee writes
    nothing outside the footprint, and a failure rolls the footprint back). -/
theorem cpiTriple_of_writes (callee : CalleeSemantics) (v : Nat) (rd : ByteArray)
    (cells : List (Nat × Nat)) (hW : writesOnly callee (cells.map Prod.fst)) :
    cpiTriple callee ((.r0 ↦ᵣ v) ** returnDataIs rd ** bytesAt cells)
      (fun r => (.r0 ↦ᵣ r.code) ** returnDataIs r.returnData ** bytesAt (commitCells r cells)) := by
  intro R hR s r hPre hCallee
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hPc, hRh2⟩ := hPre
  obtain ⟨hnd, rfl⟩ := (fpState_iff v rd cells h1).mp hPc
  have hc1 := CompatibleWith.of_union_left hcompat hu12
  have hc2 := CompatibleWith.of_union_right hcompat hu12 hd12
  have h2r0 : h2.regs .r0 = none := (hd12.regs .r0).resolve_left (by simp)
  have h2rd : h2.returnData = none := hd12.returnData.resolve_left (by simp)
  have h2pc : h2.pc = none := hR h2 hRh2
  have h2mem : ∀ a, (cells.lookup a).isSome → h2.mem a = none := by
    intro a ha
    exact (hd12.mem a).resolve_left (by simpa using ha)
  refine ⟨(fpState r.code r.returnData (commitCells r cells)).union h2, compat_union ?_ ?_,
    _, h2, ?_, rfl,
    (fpState_iff _ _ _ _).mpr ⟨by rw [commitCells_keys]; exact hnd, rfl⟩, hRh2⟩
  · -- the new footprint is compatible with the post-CPI state
    exact
      { regs := fun reg w h => by
          by_cases hreg : reg = .r0
          · subst hreg; simp at h; subst h; rfl
          · simp [hreg] at h
        mem := fun a w h => by
          simp only [fpState_mem, lookup_commitCells] at h
          cases e : cells.lookup a with
          | none => rw [e] at h; cases h
          | some o =>
            rw [e] at h; simp only [Option.map_some] at h; cases h
            have hold : s.mem a = o := hc1.mem a o (by simpa using e)
            by_cases hcode : r.code = 0
            · simp [committedByte, applyResult, hcode]
            · simp [committedByte, applyResult, hcode, hold]
        pc := fun w h => by simp at h
        returnData := fun w h => by simp at h; subst h; rfl
        callStack := fun w h => by simp at h }
  · -- the frame survives: nothing outside the footprint changes
    exact
      { regs := fun reg w h => by
          have hreg : reg ≠ .r0 := by rintro rfl; rw [h2r0] at h; cases h
          rw [← hc2.regs reg w h]
          cases reg <;> first | exact absurd rfl hreg | rfl
        mem := fun a w h => by
          have hnot : a ∉ cells.map Prod.fst := by
            intro hmem
            obtain ⟨o, ho⟩ := lookup_isSome_of_mem hmem
            rw [h2mem a (by simp [ho])] at h; cases h
          have hkeep := hW s r hCallee a hnot
          rw [← hc2.mem a w h]
          by_cases hcode : r.code = 0
          · simp [applyResult, hcode, hkeep]
          · simp [applyResult, hcode]
        pc := fun w h => by rw [h2pc] at h; cases h
        returnData := fun w h => by rw [h2rd] at h; cases h
        callStack := fun w h => hc2.callStack w h }
  · exact
      { regs := fun reg => by
          by_cases hreg : reg = .r0
          · subst hreg; exact Or.inr h2r0
          · exact Or.inl (by simp [hreg])
        mem := fun a => by
          cases e : cells.lookup a with
          | none => exact Or.inl (by simp [lookup_commitCells, e])
          | some o => exact Or.inr (h2mem a (by simp [e]))
        pc := Or.inl rfl
        returnData := Or.inr h2rd
        callStack := Or.inl rfl }

/-- A caller path across one CPI: prefix from `entry` to the invoke at
    `invokePc`, the CPI transition, and a suffix from `invokePc + 1` to
    `exit_`. For every transition the callee contract admits there is a
    result `r`; whenever `r` satisfies the path guard `G` (e.g. `r.code = 0`
    for the success path) and the remaining budget covers the suffix, the
    suffix reaches `exit_` in `Post r ** R`. The suffix budget is stated on
    the post-CPI state because the callee's compute usage is part of `r`. -/
def cpiPathWithinMem (N1 M1 entry invokePc N2 M2 exit_ : Nat) (cr1 cr2 : CodeReq)
    (P : Assertion) (Post : CalleeResult → Assertion)
    (rr1 rr2 : Memory.RegionTable → Prop) (sc : Syscall)
    (callee : CalleeSemantics) (G : CalleeResult → Prop) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn),
    (cr1.union (CodeReq.singleton invokePc (.call sc))).SatisfiedBy fetch →
    cr2.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + N1 + M1 ≤ s.cuBudget → rr1 s.regions → rr2 s.regions →
    ∃ k1, k1 ≤ N1 ∧
      (executeFn fetch s k1).pc = invokePc ∧
      fetch invokePc = some (.call sc) ∧
      (executeFn fetch s k1).exitCode = none ∧
      ∀ s', Transitions callee (executeFn fetch s k1) s' →
        ∃ r, callee (executeFn fetch s k1) r ∧ s' = applyResult (executeFn fetch s k1) r ∧
          (G r → s'.cuConsumed + N2 + M2 ≤ s'.cuBudget →
            ∃ k2, k2 ≤ N2 ∧
              (executeFn fetch s' k2).pc = exit_ ∧
              (executeFn fetch s' k2).exitCode = none ∧
              (executeFn fetch s' k2).cuConsumed ≤ s'.cuConsumed + N2 + M2 ∧
              (Post r ** R).holdsFor (executeFn fetch s' k2))

/-- Compose a prefix triple ending at the invoke (post `Pc ** F`), a CPI
    contract `cpiTriple callee Pc Qc`, and a guarded suffix triple from
    `invokePc + 1` (pre `Qc r ** F`) into one caller path across the CPI. -/
theorem cpi_path_compose
    {N1 M1 entry invokePc N2 M2 exit_ : Nat} {cr1 cr2 : CodeReq}
    {P Pc F : Assertion} {Qc Post : CalleeResult → Assertion}
    {rr1 rr2 : Memory.RegionTable → Prop} {callee : CalleeSemantics}
    {G : CalleeResult → Prop}
    (hPre : cuTripleWithinMem N1 M1 entry invokePc cr1 P (Pc ** F) rr1)
    (hFresh : cr1 invokePc = none) (hF : F.pcFree)
    (hC : cpiTriple callee Pc Qc)
    (hSuf : ∀ r, G r →
      cuTripleWithinMem N2 M2 (invokePc + 1) exit_ cr2 (Qc r ** F) (Post r) rr2)
    (sc : Syscall) :
    cpiPathWithinMem N1 M1 entry invokePc N2 M2 exit_ cr1 cr2 P Post rr1 rr2 sc callee G := by
  intro R hR fetch hcr1 hcr2 s hP hpc hex hbud hrr1 hrr2
  have hInv : fetch invokePc = some (.call sc) := by
    apply hcr1 invokePc
    show (match cr1 invokePc with | some i => some i | none => _) = _
    rw [hFresh]
    exact CodeReq.singleton_self
  obtain ⟨k1, hk1, hpc1, hex1, _, hQ⟩ :=
    hPre R hR fetch (CodeReq.SatisfiedBy_of_union_left hcr1) s hP hpc hex hbud hrr1
  refine ⟨k1, hk1, hpc1, hInv, hex1, ?_⟩
  rintro s' ⟨r, hr, rfl⟩
  refine ⟨r, hr, rfl, fun hG hbud2 => ?_⟩
  have hMid := hC (F ** R) (pcFree_sepConj hF hR) _ r (holdsFor_sepConj_assoc.mp hQ) hr
  exact hSuf r hG R hR fetch hcr2 _ (holdsFor_sepConj_assoc.mpr hMid)
    (by simp [applyResult, hpc1]) (by simp [applyResult, hex1]) hbud2
    (by simp [applyResult, executeFn_preserves_regions, hrr2])

end Cpi
end SVM.SBPF
