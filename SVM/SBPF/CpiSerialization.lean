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
