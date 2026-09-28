import SVM.SBPF.Runner

/-!
# CPI input serialization: read lemmas

When the runner executes a CPI it serializes the callee's accounts into a
fresh input buffer (`Runner.buildCpiSubInputN`) and overlays it at
`INPUT_START` (`Runner.loadInput`). This module proves where an account's
data bytes land in that buffer and that `loadInput` reads them back, so a
callee's lifted precondition can be discharged on the sub-VM state.

Performance: the proofs never compute `zeroBytes MAX_PERMITTED_DATA_INCREASE`
(10240 bytes). Every size is obtained from the generic `foldl`-push size
lemmas below and every read goes through `get!`-over-`++` lemmas.
-/

namespace SVM.SBPF
namespace Runner

open Memory

/-! ## `ByteArray` helpers -/

theorem get!_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  show (a ++ b).data[i]! = a.data[i]!
  have h' : i < (a ++ b).data.size := by
    simp only [ByteArray.data_append, Array.size_append]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  have ha : i < a.data.size := h
  rw [getElem!_pos (a ++ b).data i h', getElem!_pos a.data i ha]
  simp only [ByteArray.data_append]
  exact Array.getElem_append_left ha

theorem get!_append_right (a b : ByteArray) (i : Nat) (h : a.size ≤ i) :
    (a ++ b).get! i = b.get! (i - a.size) := by
  show (a ++ b).data[i]! = b.data[i - a.size]!
  simp only [ByteArray.data_append]
  have ha : a.data.size ≤ i := h
  by_cases hb : i - a.size < b.data.size
  · have h' : i < (a.data ++ b.data).size := by
      rw [Array.size_append]; have : a.size = a.data.size := rfl; omega
    rw [getElem!_pos (a.data ++ b.data) i h', getElem!_pos b.data (i - a.size) hb]
    exact Array.getElem_append_right ha
  · have h' : ¬ i < (a.data ++ b.data).size := by
      rw [Array.size_append]; have : a.size = a.data.size := rfl; omega
    rw [getElem!_neg (a.data ++ b.data) i h', getElem!_neg b.data (i - a.size) hb]

/-- Size of an array built by pushing one element per list entry. -/
theorem foldl_push_size {α β : Type} (l : List α) (f : α → β) (init : Array β) :
    (l.foldl (fun acc i => acc.push (f i)) init).size = init.size + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, Array.size_push]; omega

@[simp] theorem u64ToLE_size (n : Nat) : (u64ToLE n).size = 8 := by
  exact (foldl_push_size (List.range 8)
    (fun i => ((n / 256^i) % 256).toUInt8) #[]).trans (by simp)

@[simp] theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := by
  exact (foldl_push_size (List.range n) (fun _ => (0 : UInt8)) #[]).trans
    (by simp)

/-! ## Slot table and block layout -/

theorem buildAcctSlots_single (p : ParsedAcct) :
    buildAcctSlots [p] = [{ parsed := p, dupOf? := none, blockOff := 8 }] := by
  simp [buildAcctSlots, List.range, List.range.loop, List.foldl]

/-- Public equation for the non-dup block layout. -/
theorem emitNonDupBlock_eq (p : ParsedAcct) :
    emitNonDupBlock p =
      ByteArray.empty.push 0xFF
        ++ ⟨#[if p.isSigner then 1 else 0, if p.isWritable then 1 else 0,
              if p.executable then 1 else 0]⟩
        ++ zeroBytes 4 ++ p.key ++ p.owner
        ++ u64ToLE p.lamports ++ u64ToLE p.dataLen ++ p.data
        ++ zeroBytes ((8 - p.dataLen % 8) % 8)
        ++ zeroBytes MAX_PERMITTED_DATA_INCREASE ++ u64ToLE p.rentEpoch := rfl

/-- Size of the 88-byte non-dup block header (dup marker through data_len). -/
theorem nonDupHeader_size (p : ParsedAcct)
    (hsz : p.key.size = 32 ∧ p.owner.size = 32) :
    (ByteArray.empty.push 0xFF
        ++ (⟨#[if p.isSigner then 1 else 0, if p.isWritable then 1 else 0,
              if p.executable then 1 else 0]⟩ : ByteArray)
        ++ zeroBytes 4 ++ p.key ++ p.owner
        ++ u64ToLE p.lamports ++ u64ToLE p.dataLen).size = CPI_BLOCK_DATA_OFFSET := by
  have h1 : (ByteArray.empty.push 0xFF).size = 1 := rfl
  have h3 : (⟨#[if p.isSigner then 1 else 0, if p.isWritable then 1 else 0,
              if p.executable then 1 else 0]⟩ : ByteArray).size = 3 := rfl
  simp only [ByteArray.size_append, h1, h3, zeroBytes_size, u64ToLE_size,
    hsz.1, hsz.2, CPI_BLOCK_DATA_OFFSET]

/-- Byte `CPI_BLOCK_DATA_OFFSET + i` of a non-dup block is data byte `i`,
    and the block extends past it. -/
theorem emitNonDupBlock_data (p : ParsedAcct) (i : Nat) (hi : i < p.data.size)
    (hsz : p.key.size = 32 ∧ p.owner.size = 32) :
    CPI_BLOCK_DATA_OFFSET + i < (emitNonDupBlock p).size ∧
    (emitNonDupBlock p).get! (CPI_BLOCK_DATA_OFFSET + i) = p.data.get! i := by
  rw [emitNonDupBlock_eq]
  have hH := nonDupHeader_size p hsz
  -- Opaque-ify every segment (never compute the 10240-byte pad).
  generalize (ByteArray.empty.push 0xFF
        ++ (⟨#[if p.isSigner then 1 else 0, if p.isWritable then 1 else 0,
              if p.executable then 1 else 0]⟩ : ByteArray)
        ++ zeroBytes 4 ++ p.key ++ p.owner
        ++ u64ToLE p.lamports ++ u64ToLE p.dataLen) = H at hH ⊢
  generalize zeroBytes ((8 - p.dataLen % 8) % 8) = A
  generalize zeroBytes MAX_PERMITTED_DATA_INCREASE = Z
  generalize u64ToLE p.rentEpoch = R
  refine ⟨by simp only [ByteArray.size_append]; omega, ?_⟩
  rw [get!_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      get!_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      get!_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      get!_append_right _ _ _ (by omega), hH, Nat.add_sub_cancel_left]

/-- The single non-dup slot `buildAcctSlots [p]` produces. -/
abbrev slot1 (p : ParsedAcct) : AcctSlot :=
  { parsed := p, dupOf? := none, blockOff := 8 }

/-- Data byte `i` of the sole account sits at `8 + CPI_BLOCK_DATA_OFFSET + i`
    of the serialized CPI sub-input. -/
theorem buildCpiSubInputN_first_data (p : ParsedAcct) (pid ix : ByteArray)
    (i : Nat) (hi : i < p.data.size)
    (hsz : p.key.size = 32 ∧ p.owner.size = 32) :
    (buildCpiSubInputN [{ parsed := p, dupOf? := none, blockOff := 8 }] pid ix).get!
        (8 + CPI_BLOCK_DATA_OFFSET + i) = p.data.get! i := by
  obtain ⟨hlt, hget⟩ := emitNonDupBlock_data p i hi hsz
  simp only [buildCpiSubInputN, List.foldl_cons, List.foldl_nil,
    ByteArray.empty_append]
  generalize emitNonDupBlock p = E at hlt hget ⊢
  have h8 : ∀ k, (u64ToLE k).size = 8 := u64ToLE_size
  rw [get!_append_left _ _ _ (by simp only [ByteArray.size_append, h8]; omega),
      get!_append_left _ _ _ (by simp only [ByteArray.size_append, h8]; omega),
      get!_append_left _ _ _ (by simp only [ByteArray.size_append, h8]; omega),
      get!_append_right _ _ _ (by simp only [h8]; omega), h8]
  rw [show 8 + CPI_BLOCK_DATA_OFFSET + i - 8 = CPI_BLOCK_DATA_OFFSET + i by omega]
  exact hget

/-! ## `loadInput` read-back -/

theorem loadBytesAt_read (mem : Mem) (bytes : ByteArray) (base a : Nat) :
    (loadBytesAt mem bytes base) a =
      if base ≤ a ∧ a < base + bytes.size then
        (bytes.get! (a - base)).toNat % 256
      else mem a := by
  unfold loadBytesAt Memory.writeU8
  generalize bytes.size = n
  induction n with
  | zero => simp; omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    show Mem.read (Mem.put _ _ _) a = _
    by_cases hx : a = base + n
    · subst hx
      rw [Mem.read_put_self]
      simp
    · rw [Mem.read_put_other _ _ _ _ hx]
      rw [ih]
      by_cases h1 : base ≤ a ∧ a < base + n
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem loadInput_read (mem : Mem) (input : ByteArray) (a : Nat)
    (ha : a < input.size) :
    loadInput mem input (INPUT_START + a) = (input.get! a).toNat := by
  unfold loadInput
  rw [loadBytesAt_read, if_pos (by omega), Nat.add_sub_cancel_left]
  exact Nat.mod_eq_of_lt (input.get! a).toNat_lt

theorem loadInput_read_outside {mem : Mem} {input : ByteArray} {a : Nat}
    (ha : ¬ (INPUT_START ≤ a ∧ a < INPUT_START + input.size)) :
    loadInput mem input a = mem a := by
  unfold loadInput
  rw [loadBytesAt_read, if_neg ha]

/-! ## Write-back (`commitCallee`) read lemmas

After the callee runs, `commitCallee` folds over the slots and, for each
writable non-dup slot, writes the post-call data (`postLen` bytes at
`dataPtr`), both `data_len` slots (`dataLenRefAddr`, `dataPtr - 8`), the
lamports and the owner back into caller memory. A violation (realloc past
`dataLen + MAX_PERMITTED_DATA_INCREASE`, or a modified read-only account)
returns `callerMem` unchanged. -/

theorem foldl_push_range_eq {β : Type} (f : Nat → β) (n : Nat) :
    (List.range n).foldl (fun acc i => acc.push (f i)) #[] = ((List.range n).map f).toArray := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp

theorem readMemBytes_size (mem : Mem) (addr len : Nat) :
    (readMemBytes mem addr len).size = len := by
  unfold readMemBytes
  exact (foldl_push_size (List.range len) _ #[]).trans (by simp)

theorem readMemBytes_get! (mem : Mem) (addr len i : Nat) (hi : i < len) :
    (readMemBytes mem addr len).get! i = ((mem (addr + i)) % 256).toUInt8 := by
  unfold readMemBytes
  show (_ : Array UInt8)[i]! = _
  rw [foldl_push_range_eq]
  simp [hi]

/-- The bytes one writable non-dup slot's write-back may touch: the data
    range up to the realloc bound (a committed `postLen` never exceeds
    `dataLen + MAX_PERMITTED_DATA_INCREASE`), both `data_len` slots
    (`dataLenRefAddr` and `dataPtr - 8`, truncated subtraction as in
    `commitCallee`), lamports and owner. -/
def slotWriteBack (p : ParsedAcct) (a : Nat) : Prop :=
  (p.dataPtr ≤ a ∧ a < p.dataPtr + p.dataLen + MAX_PERMITTED_DATA_INCREASE) ∨
  (p.dataLenRefAddr ≤ a ∧ a < p.dataLenRefAddr + 8) ∨
  (p.dataPtr - 8 ≤ a ∧ a < p.dataPtr - 8 + 8) ∨
  (p.lamportsRefAddr ≤ a ∧ a < p.lamportsRefAddr + 8) ∨
  (p.ownerPtr ≤ a ∧ a < p.ownerPtr + 32)

/-- Every byte `commitCallee` may write for `slots`. -/
def writeBackFootprint (slots : List AcctSlot) (a : Nat) : Prop :=
  ∃ slot ∈ slots, slot.dupOf? = none ∧ slot.parsed.isWritable = true ∧
    slotWriteBack slot.parsed a

theorem writeU64_read_outside (mem : Mem) (addr val a : Nat)
    (h : ¬ (addr ≤ a ∧ a < addr + 8)) : (writeU64 mem addr val) a = mem a :=
  writeU64_read_other mem addr val a (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)

/-- A fold whose step preserves address `a` for every element outside `P`
    preserves `a`. -/
theorem foldl_frame {α : Type} (f : Mem → α → Mem) (P : α → Prop) (a : Nat) :
    ∀ (l : List α) (mem : Mem), (∀ x ∈ l, ∀ m, ¬ P x → f m x a = m a) →
      (∀ x ∈ l, ¬ P x) → (l.foldl f mem) a = mem a
  | [], _, _, _ => rfl
  | x :: xs, mem, hf, hP => by
    rw [List.foldl_cons, foldl_frame f P a xs _ (fun y hy => hf y (List.mem_cons_of_mem _ hy))
      (fun y hy => hP y (List.mem_cons_of_mem _ hy))]
    exact hf x List.mem_cons_self _ (hP x List.mem_cons_self)

/-- `commitCallee` leaves caller memory outside the write-back footprint
    untouched (on every branch: violations return `callerMem`). -/
theorem commitCallee_mem_outside (callerMem : Mem) (slots : List AcctSlot) (subFinal : State)
    (f a : Nat) (ha : ¬ writeBackFootprint slots a) :
    (commitCallee callerMem slots subFinal f).2.1 a = callerMem a := by
  unfold commitCallee
  extract_lets roV reV newMem
  split
  · rfl
  split
  · rfl
  rename_i hre _
  show newMem a = callerMem a
  have hbound : ∀ slot ∈ slots, slot.dupOf? = none → slot.parsed.isWritable = true →
      Memory.readU64 subFinal.mem (INPUT_START + slot.blockOff + CPI_BLOCK_DATALEN_OFFSET)
        ≤ slot.parsed.dataLen + MAX_PERMITTED_DATA_INCREASE := by
    intro slot hs hd hw
    have := hre
    simp only [reV, List.any_eq_true, not_exists, not_and] at this
    have h := this slot hs
    rw [hd] at h
    simp only [hw, Bool.not_true, Bool.false_eq_true, if_false, decide_eq_true_eq] at h
    omega
  refine foldl_frame _ (fun slot => slot.dupOf? = none ∧ slot.parsed.isWritable = true ∧
      slotWriteBack slot.parsed a) a slots callerMem ?_ ?_
  · intro slot hs m hn
    simp only
    split
    · rfl
    rename_i hd
    by_cases hw : slot.parsed.isWritable = true
    · simp only [hw, Bool.not_true, Bool.false_eq_true, if_false]
      have hb := hbound slot hs hd hw
      simp only [slotWriteBack, hd, hw, true_and] at hn
      rw [loadBytesAt_read, readMemBytes_size, if_neg (by omega), writeU64_read_outside _ _ _ _ (by omega),
        writeU64_read_outside _ _ _ _ (by omega), writeU64_read_outside _ _ _ _ (by omega),
        loadBytesAt_read, readMemBytes_size, if_neg (by omega)]
    · simp [hw]
  · intro slot hs h
    exact ha ⟨slot, hs, h⟩

/-- For a single writable account whose post-call length is unchanged, the
    committed data byte `i` is the callee's final byte at the sole block's
    data offset (mod 256, as `readMemBytes`/`loadBytesAt` store bytes). The
    later length/lamports/owner writes are excluded by the disjointness
    hypotheses. -/
theorem commitCallee_data (callerMem : Mem) (slots : List AcctSlot) (subFinal : State)
    (f : Nat) (p : ParsedAcct) (i : Nat)
    (hslots : slots = [slot1 p])
    (hw : p.isWritable = true)
    (hlen : Memory.readU64 subFinal.mem (INPUT_START + 8 + CPI_BLOCK_DATALEN_OFFSET) = p.dataLen)
    (hi : i < p.dataLen)
    (hdl : ¬ (p.dataLenRefAddr ≤ p.dataPtr + i ∧ p.dataPtr + i < p.dataLenRefAddr + 8))
    (hdp : 8 ≤ p.dataPtr)
    (hlam : ¬ (p.lamportsRefAddr ≤ p.dataPtr + i ∧ p.dataPtr + i < p.lamportsRefAddr + 8))
    (hown : ¬ (p.ownerPtr ≤ p.dataPtr + i ∧ p.dataPtr + i < p.ownerPtr + 32)) :
    (commitCallee callerMem slots subFinal f).2.1 (p.dataPtr + i) =
      subFinal.mem (INPUT_START + 8 + CPI_BLOCK_DATA_OFFSET + i) % 256 := by
  subst hslots
  unfold commitCallee
  simp only [List.any_cons, List.any_nil, Bool.or_false, slot1, hw, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, hlen, List.foldl_cons, List.foldl_nil]
  rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
  rw [loadBytesAt_read, readMemBytes_size, if_neg (by omega), writeU64_read_outside _ _ _ _ hlam,
    writeU64_read_outside _ _ _ _ (by omega), writeU64_read_outside _ _ _ _ hdl,
    loadBytesAt_read, readMemBytes_size, if_pos (by omega), Nat.add_sub_cancel_left,
    readMemBytes_get! _ _ _ _ hi]
  simp
/-- A successful callee build lays out exactly `buildAcctSlots` of the
    accounts it was given. -/
theorem buildCalleeVM_slots {s : State} {fuel' : Nat} {pid : ByteArray} {accts : List ParsedAcct}
    {ix bytes : ByteArray} {insns : Array Insn} {t : State} {slots : List AcctSlot}
    (h : buildCalleeVM s fuel' pid accts ix bytes = some (insns, t, slots)) :
    slots = buildAcctSlots accts := by
  unfold buildCalleeVM at h
  extract_lets tryElf isElf sl subInput baseMem jp at h
  have hjp : ∀ x i t' sl', jp x = some (i, t', sl') → sl' = sl := by
    intro x i t' sl' hx
    rcases x with ⟨a, b, c, d, e⟩
    simp only [jp, bind, Option.bind] at hx
    split at hx
    · cases hx
    · cases hx; rfl
  repeat' (first
    | exact hjp _ _ _ _ h
    | (obtain ⟨_, _, h⟩ := h)
    | (cases h; done)
    | split at h
    | simp only [bind, Option.bind_eq_some_iff] at h)
/-! ## Concrete regression -/

private def demoAcct : ParsedAcct :=
  { key := ⟨Array.replicate 32 1⟩, owner := ⟨Array.replicate 32 2⟩,
    lamports := 5, dataLen := 2, data := ⟨#[7, 9]⟩,
    isSigner := true, isWritable := true, executable := false, rentEpoch := 0,
    ownerPtr := 0, lamportsRefAddr := 0, dataPtr := 0, dataLenRefAddr := 0 }

example : buildAcctSlots [demoAcct] = [slot1 demoAcct] :=
  buildAcctSlots_single demoAcct

example : (buildCpiSubInputN [slot1 demoAcct] ByteArray.empty ByteArray.empty).get!
    (8 + CPI_BLOCK_DATA_OFFSET + 0) = 7 := by native_decide

example : (buildCpiSubInputN [slot1 demoAcct] ByteArray.empty ByteArray.empty).get!
    (8 + CPI_BLOCK_DATA_OFFSET + 1) = 9 := by native_decide

example : loadInput emptyMem
    (buildCpiSubInputN [slot1 demoAcct] ByteArray.empty ByteArray.empty)
    (INPUT_START + (8 + CPI_BLOCK_DATA_OFFSET + 0)) = 7 := by native_decide

example : loadInput emptyMem
    (buildCpiSubInputN [slot1 demoAcct] ByteArray.empty ByteArray.empty)
    (INPUT_START + (8 + CPI_BLOCK_DATA_OFFSET + 1)) = 9 := by native_decide

end Runner
end SVM.SBPF
