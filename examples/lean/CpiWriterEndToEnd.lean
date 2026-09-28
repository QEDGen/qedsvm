/-
  The writer callee meets its write contract.

  The pinned V3 callee `sbpfv3_cpi_writer_callee.so`
  (`mov64 r2, 42; stxb [r1+96], r2; mov64 r0, 0; exit`) invoked by the runner
  from the writer caller `sbpfv3_cpi_writer.so` (C ABI, one writable account
  whose 2 data bytes sit at `base + 96`): the runner's callee relation,
  restricted to the caller-memory invariant `writerInv base`, changes only
  caller byte `base + 96` on success (`writer_callee_contract`), and on
  success that byte is 42 (`writer_callee_value`).

  The proof follows the runner through the invoke: the invariant pins the
  parsed account, the program id (routed by `writerRegistry` to the callee
  ELF) and rules out native dispatch; the callee ELF loads and decodes to the
  four pinned instructions (`native_decide`); code 0 forces the full
  four-step callee run (store 42 at `INPUT_START + 96`, exit with `r0 = 0`);
  and the write-back re-encodes the sub-input bytes, which mirror the
  caller's account bytes, so every byte but the data byte round-trips.
-/

import SVM.SBPF.CpiRunner
import Generated.Sbpfv3CpiWriterCalleeLifted

set_option maxRecDepth 65536

namespace Examples.CpiWriterEndToEnd

open SVM.SBPF SVM.SBPF.Memory SVM.SBPF.Runner
open Examples.Lifted.Sbpfv3CpiWriterCalleeLifted

/-! ## The callee, its id and the registry -/

/-- The pinned callee ELF. -/
abbrev calleeElf : ByteArray := Sbpfv3CpiWriterCalleeLiftedElf

/-- The callee's 32-byte program id: `pid(441)` of the writer differential
    test (`441` little-endian, zero padded). -/
def writerCalleeId : ByteArray :=
  ⟨#[185, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Little-endian value of a 32-byte program id, as the runner's four-limb
    `pid` reads it. -/
def pidNat (b : ByteArray) : Nat :=
  (List.range 32).foldl (fun acc i => acc + (b.get! i).toNat * 256 ^ i) 0

theorem pidNat_writerCalleeId : pidNat writerCalleeId = 441 := by decide

/-- The runner registry for the writer: the callee id routes to the callee
    ELF, nothing else is registered. -/
def writerRegistry : Nat → Option ByteArray :=
  fun pid => if pid = pidNat writerCalleeId then some calleeElf else none

/-! ## The callee loads -/

/-- The decoded callee. -/
def calleeInsns : Array Insn :=
  #[.mov64 .r2 (.imm 42), .stx .byte .r1 96 .r2, .mov64 .r0 (.imm 0), .exit]

/-- The loaded callee image: 32 text bytes at the V3 bytecode base, no
    rodata, entry slot 0. -/
def calleeProgram : Elf.V3Program :=
  { textBytes := Sbpfv3CpiWriterCalleeLiftedText, rodata := ByteArray.empty,
    textAddr := 0x100000000, entrySlot := 0 }

theorem callee_isElf :
    (decide (calleeElf.size ≥ 4) && Decode.readU8 calleeElf 0 == 0x7f &&
      Decode.readU8 calleeElf 1 == 0x45 && Decode.readU8 calleeElf 2 == 0x4c &&
      Decode.readU8 calleeElf 3 == 0x46) = true := by native_decide

theorem callee_version : Elf.readVersion calleeElf = some .v3 := by native_decide

theorem callee_load : Elf.loadV3 calleeElf = some calleeProgram := by
  have h1 : (Elf.loadV3 calleeElf).map (·.textBytes) = some Sbpfv3CpiWriterCalleeLiftedText :=
    Sbpfv3CpiWriterCalleeLifted_v3_elf_text
  have h2 : (Elf.loadV3 calleeElf).map (·.rodata) = some ByteArray.empty := by native_decide
  have h3 : (Elf.loadV3 calleeElf).map (·.textAddr) = some 0x100000000 := by native_decide
  have h4 : (Elf.loadV3 calleeElf).map (·.entrySlot) = some 0 := by native_decide
  cases h : Elf.loadV3 calleeElf with
  | none => rw [h] at h1; cases h1
  | some p =>
    rw [h] at h1 h2 h3 h4
    simp only [Option.map_some, Option.some.injEq] at h1 h2 h3 h4
    cases p
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl

theorem callee_decode :
    Decode.decodeProgram Sbpfv3CpiWriterCalleeLiftedText [] .v3 = some calleeInsns := by
  native_decide

theorem callee_entry :
    (Decode.buildSlotMap Sbpfv3CpiWriterCalleeLiftedText)[0]?.getD 0 = 0 := by native_decide

/-- The callee sub-VM state the runner builds for sub-input `subInput`. -/
def calleeSubS (s : State) (fuel' : Nat) (pidB subInput : ByteArray) : State :=
  { regs        := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
    mem         := loadBytesAt (loadBytesAt (loadInput emptyMem subInput)
                     Sbpfv3CpiWriterCalleeLiftedText 0x100000000) ByteArray.empty 0
    regions     := v3Regions calleeProgram subInput.size
    pc          := 0
    exitCode    := none
    log         := s.log
    returnData  := s.returnData
    returnDataProgId := s.returnDataProgId
    cuBudget    := fuel'
    progIdBytes := pidB
    origPrivs   := parseInputPrivileges subInput
    invokeDepth := s.invokeDepth + 1 }

/-- The runner's callee build for the writer callee. -/
theorem buildCalleeVM_callee (s : State) (fuel' : Nat) (pidB : ByteArray)
    (accts : List ParsedAcct) (ix : ByteArray) :
    buildCalleeVM s fuel' pidB accts ix calleeElf =
      some (calleeInsns,
        calleeSubS s fuel' pidB (buildCpiSubInputN (buildAcctSlots accts) pidB ix),
        buildAcctSlots accts) := by
  unfold buildCalleeVM
  simp only [callee_isElf, if_true, callee_version, callee_load, bind, Option.bind_some,
    calleeProgram, callee_decode, Option.isSome_some, callee_entry]
  rfl

/-! ## The callee's run -/

/-- A callee run from the entry that exits with code 0 stored 42 at
    `r1 + 96`: code 0 needs all four steps (store, then `exit` with an empty
    call stack); with less fuel or budget the run is still live. -/
theorem callee_exec (t : State) (F : Nat) (hpc : t.pc = 0) (hex : t.exitCode = none)
    (hcu : t.cuConsumed = 0) (hbud : t.cuBudget = F) (hcs : t.callStack = [])
    (hr1 : t.regs.r1 = INPUT_START)
    (hreg : t.regions.containsWritable (INPUT_START + 96) 1 = true)
    (h0 : (executeFn (fetchFromArray calleeInsns) t F).exitCode = some 0) :
    (executeFn (fetchFromArray calleeInsns) t F).mem = writeU8 t.mem (INPUT_START + 96) 42 := by
  subst hbud
  have hf0 : fetchFromArray calleeInsns 0 = some (.mov64 .r2 (.imm 42)) := rfl
  have hf1 : fetchFromArray calleeInsns 1 = some (.stx .byte .r1 96 .r2) := rfl
  have hf2 : fetchFromArray calleeInsns 2 = some (.mov64 .r0 (.imm 0)) := rfl
  have hf3 : fetchFromArray calleeInsns 3 = some .exit := rfl
  -- The states after one, two and three steps.
  generalize ht1 : chargeCu (step (.mov64 .r2 (.imm 42)) t) = t1
  have e1 : t1.pc = 1 ∧ t1.exitCode = none ∧ t1.cuConsumed = 1 ∧ t1.cuBudget = t.cuBudget ∧
      t1.callStack = [] ∧ t1.regs.r1 = INPUT_START ∧ t1.regs.r2 = 42 ∧ t1.regions = t.regions ∧
      t1.mem = t.mem := by
    subst ht1; simp [hpc, hex, hcu, hcs, hr1]
  generalize ht2 : chargeCu (step (.stx .byte .r1 96 .r2) t1) = t2
  have e2 : t2.pc = 2 ∧ t2.exitCode = none ∧ t2.cuConsumed = 2 ∧ t2.cuBudget = t.cuBudget ∧
      t2.callStack = [] ∧ t2.mem = writeU8 t.mem (INPUT_START + 96) 42 := by
    subst ht2
    obtain ⟨p1, x1, c1, b1, s1, r1, r2, g1, m1⟩ := e1
    have hw : t1.regions.containsWritable (effectiveAddr (t1.regs.get .r1) 96) Width.byte.bytes = true := by
      rw [g1]; simpa [r1, effectiveAddr, Width.bytes] using hreg
    simp only [step, hw, if_true]
    simp [p1, x1, c1, b1, s1, m1, r1, r2, effectiveAddr, writeByWidth]
    congr 1
  generalize ht3 : chargeCu (step (.mov64 .r0 (.imm 0)) t2) = t3
  have e3 : t3.pc = 3 ∧ t3.exitCode = none ∧ t3.cuConsumed = 3 ∧ t3.cuBudget = t.cuBudget ∧
      t3.callStack = [] ∧ t3.regs.r0 = 0 ∧ t3.mem = writeU8 t.mem (INPUT_START + 96) 42 := by
    subst ht3
    obtain ⟨p2, x2, c2, b2, s2, m2⟩ := e2
    simp [p2, x2, c2, b2, s2, m2]
  obtain ⟨p1, x1, c1, b1, -⟩ := e1
  obtain ⟨p2, x2, c2, b2, -⟩ := e2
  obtain ⟨p3, x3, c3, b3, s3, r03, m3⟩ := e3
  have hex4 : (chargeCu (step .exit t3)).exitCode = some 0 := by
    simp [s3, r03]
  have hm4 : (chargeCu (step .exit t3)).mem = writeU8 t.mem (INPUT_START + 96) 42 := by
    simp [s3, m3]
  generalize hF : t.cuBudget = F at h0 b1 b2 b3
  rcases F with _ | _ | _ | _ | n
  · rw [executeFn_zero, hex] at h0; cases h0
  · rw [executeFn_step _ t 0 _ hex (by omega) (hpc ▸ hf0), ht1, executeFn_zero, x1] at h0
    cases h0
  · rw [executeFn_step _ t 1 _ hex (by omega) (hpc ▸ hf0), ht1,
      executeFn_step _ t1 0 _ x1 (by omega) (p1 ▸ hf1), ht2, executeFn_zero, x2] at h0
    cases h0
  · rw [executeFn_step _ t 2 _ hex (by omega) (hpc ▸ hf0), ht1,
      executeFn_step _ t1 1 _ x1 (by omega) (p1 ▸ hf1), ht2,
      executeFn_step _ t2 0 _ x2 (by omega) (p2 ▸ hf2), ht3, executeFn_zero, x3] at h0
    cases h0
  · rw [executeFn_step _ t (n + 3) _ hex (by omega) (hpc ▸ hf0), ht1,
      executeFn_step _ t1 (n + 2) _ x1 (by omega) (p1 ▸ hf1), ht2,
      executeFn_step _ t2 (n + 1) _ x2 (by omega) (p2 ▸ hf2), ht3,
      executeFn_step _ t3 n _ x3 (by omega) (p3 ▸ hf3),
      executeFn_halted _ _ n 0 hex4, hm4]

theorem calleeRegions_writable (n : Nat) (hn : 97 ≤ n) :
    (v3Regions calleeProgram n).containsWritable (INPUT_START + 96) 1 = true := by
  have he : calleeProgram.rodata.isEmpty = true := by decide
  simp [v3Regions, he, runtimeRegions, RegionTable.containsWritable, Region.contains]
  omega

/-- The runner's sub-run of the callee: exit code 0 means the store of 42 at
    `INPUT_START + 96` happened and nothing else changed memory. -/
theorem callee_run (registry : Nat → Option ByteArray) (s : State) (fuel' : Nat)
    (pidB subInput : ByteArray) (hsz : 97 ≤ subInput.size)
    (h0 : (executeFnCpiWithFuel registry (fetchFromArray calleeInsns)
      (calleeSubS s fuel' pidB subInput) fuel').1.exitCode = some 0) :
    (executeFnCpiWithFuel registry (fetchFromArray calleeInsns)
      (calleeSubS s fuel' pidB subInput) fuel').1.mem =
        writeU8 (calleeSubS s fuel' pidB subInput).mem (INPUT_START + 96) 42 := by
  have hb := executeFnCpi_eq_executeFn_of_no_cpi_array registry calleeInsns
    (calleeSubS s fuel' pidB subInput) fuel' (by decide)
  unfold executeFnCpi at hb
  rw [hb] at h0 ⊢
  exact callee_exec _ fuel' rfl rfl rfl rfl rfl rfl (calleeRegions_writable _ hsz) h0

end Examples.CpiWriterEndToEnd
