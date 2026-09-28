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
import SVM.SBPF.CodecRead
import Generated.Sbpfv3CpiWriterCalleeLifted
import Generated.Sbpfv3CpiWriterLiftedSuccess

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

/-! ## The caller-memory invariant at the invoke

The writer builds, on the heap at `0x300000000`, a C-ABI `SolInstruction`
(`+0` program id ptr, `+16` account count, `+32` data length), an
`SolAccountMeta` at `+48` and one `SolAccountInfo` at `+64` (`+0` key ptr,
`+8` lamports ptr, `+16` data_len, `+24` data ptr, `+32` owner ptr, `+49`
is_writable), all pointing into its own input at `base`: key `base + 16`,
owner `base + 48`, lamports `base + 80`, data_len `base + 88`, data
`base + 96` (2 bytes), and the callee's id (the second account's key) at
`base + 10360`. `r1`/`r2` point at the instruction/account info, `r5 = 0`
(no signer seeds). The runner reads exactly these facts at the invoke;
the byte bounds make the write-back's re-encoding of the account's owner,
lamports and length bytes an identity. -/

/-- The caller state at the writer's invoke. -/
structure writerInv (base : Nat) (s : State) : Prop where
  /-- The caller's input lies above the heap cells the runner rewrites. -/
  base_ge : 12884901888 + 88 ≤ base
  r1 : s.regs.r1 = 12884901888
  r2 : s.regs.r2 = 12884901952
  r5 : s.regs.r5 = 0
  depth : s.invokeDepth = 0
  ixProgId : readU64 s.mem 12884901888 = base + 10360
  ixAcctCount : readU64 s.mem 12884901904 = 1
  ixDataLen : readU64 s.mem 12884901920 = 0
  aiKey : readU64 s.mem 12884901952 = base + 16
  aiLamports : readU64 s.mem 12884901960 = base + 80
  aiDataLen : readU64 s.mem 12884901968 = 2
  aiData : readU64 s.mem 12884901976 = base + 96
  aiOwner : readU64 s.mem 12884901984 = base + 48
  aiWritable : s.mem 12884902001 % 256 ≠ 0
  progId : ∀ i, i < 32 → s.mem (base + 10360 + i) = (writerCalleeId.get! i).toNat
  origWritable :
    s.origPrivs.any (fun t => t.1 == readMemBytes s.mem (base + 16) 32 && t.2.2) = true
  inputDataLen : readU64 s.mem (base + 88) = 2
  inputBytes : ∀ a, base + 48 ≤ a → a < base + 98 → s.mem a < 256
  lenBytes : ∀ a, 12884901968 ≤ a → a < 12884901976 → s.mem a < 256

/-- The account the runner hands the callee. -/
def writerAcct (s : State) : ParsedAcct :=
  let raw := parseCpiAccount s.mem 12884901952
  { raw with
    isSigner := raw.isSigner && s.origPrivs.any (fun t => t.1 == raw.key && t.2.1)
    isWritable := true }

theorem writer_accts {base : Nat} {s : State} (h : writerInv base s) :
    Cpi.invokeAccts s .sol_invoke_signed_c = [writerAcct s] := by
  unfold Cpi.invokeAccts
  rw [h.r1, h.r2, h.r5, show (12884901888 : Nat) + 16 = 12884901904 from rfl, h.ixAcctCount]
  simp only [parseCpiAccounts, deriveSignerPdas, List.range_zero, List.filterMap_nil,
    clampCpiPrivileges, List.any_nil, Bool.false_or, List.range_one, List.map_cons,
    List.map_nil, Nat.zero_mul, Nat.add_zero, List.cons.injEq, and_true, writerAcct,
    ParsedAcct.mk.injEq, true_and]
  have hw : (parseCpiAccount s.mem 12884901952).isWritable = true := by
    simpa [parseCpiAccount] using h.aiWritable
  have hk : (parseCpiAccount s.mem 12884901952).key = readMemBytes s.mem (base + 16) 32 := by
    simp only [parseCpiAccount]; rw [h.aiKey]
  rw [hw, hk, h.origWritable]; rfl


section AcctFields
variable {base : Nat} {s : State}

theorem writerAcct_isWritable : (writerAcct s).isWritable = true := rfl
theorem writerAcct_dataLenRefAddr : (writerAcct s).dataLenRefAddr = 12884901968 := rfl
variable (h : writerInv base s)
include h
theorem writerAcct_dataPtr : (writerAcct s).dataPtr = base + 96 := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiData]
theorem writerAcct_dataLen : (writerAcct s).dataLen = 2 := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiDataLen]
theorem writerAcct_lamportsRefAddr : (writerAcct s).lamportsRefAddr = base + 80 := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiLamports]
theorem writerAcct_ownerPtr : (writerAcct s).ownerPtr = base + 48 := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiOwner]
theorem writerAcct_key : (writerAcct s).key = readMemBytes s.mem (base + 16) 32 := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiKey]
theorem writerAcct_owner : (writerAcct s).owner = readMemBytes s.mem (base + 48) 32 := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiOwner]
theorem writerAcct_lamports : (writerAcct s).lamports = readU64 s.mem (base + 80) := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiLamports]
theorem writerAcct_data : (writerAcct s).data = readMemBytes s.mem (base + 96) 2 := by
  simp only [writerAcct, parseCpiAccount]; rw [h.aiData, h.aiDataLen]

end AcctFields

/-! ## The program id routes to the callee, not to a native program -/

theorem readU64_of_bytes (m : Mem) (a : Nat) (b : Nat → Nat)
    (hb : ∀ i, i < 8 → m (a + i) % 256 = b i) :
    readU64 m a = b 0 + b 1 * 256 + b 2 * 65536 + b 3 * 16777216 + b 4 * 4294967296 +
      b 5 * 1099511627776 + b 6 * 281474976710656 + b 7 * 72057594037927936 := by
  unfold readU64
  rw [← hb 0 (by omega), ← hb 1 (by omega), ← hb 2 (by omega), ← hb 3 (by omega),
    ← hb 4 (by omega), ← hb 5 (by omega), ← hb 6 (by omega), ← hb 7 (by omega)]
  rfl

/-- The id's bytes: `185, 1`, then zeros. -/
theorem writerCalleeId_get! : ∀ i, i < 32 →
    (writerCalleeId.get! i).toNat = if i = 0 then 185 else if i = 1 then 1 else 0 := by
  decide

theorem writer_pid {base : Nat} {s : State} (h : writerInv base s) :
    Cpi.invokePid s .sol_invoke_signed_c = pidNat writerCalleeId := by
  let w : Nat → Nat := fun i => if i = 0 then 185 else if i = 1 then 1 else 0
  have limb : ∀ k, k < 4 → readU64 s.mem (base + 10360 + 8 * k) =
      w (8 * k) + w (8 * k + 1) * 256 + w (8 * k + 2) * 65536 + w (8 * k + 3) * 16777216 +
        w (8 * k + 4) * 4294967296 + w (8 * k + 5) * 1099511627776 +
        w (8 * k + 6) * 281474976710656 + w (8 * k + 7) * 72057594037927936 := by
    intro k hk
    rw [readU64_of_bytes s.mem _ (fun i => w (8 * k + i))]
    · rfl
    · intro i hi
      rw [show base + 10360 + 8 * k + i = base + 10360 + (8 * k + i) by omega,
        h.progId _ (by omega), Nat.mod_eq_of_lt (UInt8.toNat_lt _),
        writerCalleeId_get! _ (by omega)]
  unfold Cpi.invokePid
  simp only [h.r1, h.ixProgId]
  have l0 := limb 0 (by omega)
  have l1 := limb 1 (by omega)
  have l2 := limb 2 (by omega)
  have l3 := limb 3 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at l0
  rw [l0, show base + 10360 + 8 = base + 10360 + 8 * 1 from rfl, l1,
    show base + 10360 + 16 = base + 10360 + 8 * 2 from rfl, l2,
    show base + 10360 + 24 = base + 10360 + 8 * 3 from rfl, l3, pidNat_writerCalleeId]
  simp [w]

theorem writer_registry {base : Nat} {s : State} (h : writerInv base s) :
    writerRegistry (Cpi.invokePid s .sol_invoke_signed_c) = some calleeElf := by
  rw [writer_pid h]; simp [writerRegistry]

theorem writer_nativeNone {base : Nat} {s : State} (h : writerInv base s) :
    Cpi.invokeNativeNone s .sol_invoke_signed_c := by
  unfold Cpi.invokeNativeNone
  rw [writer_pid h, pidNat_writerCalleeId]
  simp [SVM.Native.dispatch, SVM.Native.System.PROGRAM_ID, SVM.Native.ComputeBudget.PROGRAM_ID,
    SVM.Native.BpfLoaderUpgradeable.PROGRAM_ID, SVM.Native.Precompiles.dispatch,
    SVM.Native.Precompiles.ED25519_PROGRAM_ID, SVM.Native.Precompiles.SECP256K1_PROGRAM_ID,
    SVM.Native.Precompiles.SECP256R1_PROGRAM_ID]

/-! ## The sub-input mirrors the caller's account bytes -/

theorem calleeText_size : Sbpfv3CpiWriterCalleeLiftedText.size = 32 := by native_decide

theorem toUInt8_toNat_mod (n : Nat) : (n % 256).toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8]

/-- The callee's sub-input region `[INPUT_START + 48, INPUT_START + 98)` (the
    sole account's owner, lamports, data_len and data) holds the caller's
    bytes `[base + 48, base + 98)`, mod 256. -/
theorem writer_subInput_mirror {base : Nat} {s : State} (h : writerInv base s)
    (pidB ix : ByteArray) (k : Nat) (hk1 : 48 ≤ k) (hk2 : k < 98) :
    loadBytesAt (loadBytesAt (loadInput emptyMem
        (buildCpiSubInputN (buildAcctSlots [writerAcct s]) pidB ix))
        Sbpfv3CpiWriterCalleeLiftedText 0x100000000) ByteArray.empty 0 (INPUT_START + k) =
      s.mem (base + k) % 256 := by
  rw [loadBytesAt_read, if_neg (by simp), loadBytesAt_read, if_neg (by rw [calleeText_size]; simp [INPUT_START]; omega),
    buildAcctSlots_single]
  have hsz : (writerAcct s).key.size = 32 ∧ (writerAcct s).owner.size = 32 := by
    rw [writerAcct_key h, writerAcct_owner h]; exact ⟨readMemBytes_size _ _ _, readMemBytes_size _ _ _⟩
  have hds : (writerAcct s).data.size = 2 := by rw [writerAcct_data h]; exact readMemBytes_size _ _ _
  have hge := emitNonDupBlock_size_ge (writerAcct s) hsz
  obtain ⟨hlt, hget⟩ := buildCpiSubInputN_single_get! (writerAcct s) pidB ix (k - 8)
    (by simp only [CPI_BLOCK_DATA_OFFSET] at hge; omega)
  rw [show k = 8 + (k - 8) by omega, loadInput_read _ _ _ hlt, hget,
    emitNonDupBlock_get!_header _ _ hsz (by omega)]
  split
  · rw [writerAcct_owner h, readMemBytes_get! _ _ _ _ (by omega), toUInt8_toNat_mod]
    congr 2; omega
  split
  · rw [writerAcct_lamports h, u64ToLE_get! _ _ (by omega), toUInt8_toNat_mod,
      readU64_digit _ _ _ (by omega)]
    congr 2; omega
  split
  · rw [writerAcct_dataLen h, ← h.inputDataLen, u64ToLE_get! _ _ (by omega), toUInt8_toNat_mod,
      readU64_digit _ _ _ (by omega)]
    congr 2; omega
  · rw [writerAcct_data h, readMemBytes_get! _ _ _ _ (by omega), toUInt8_toNat_mod]
    congr 2; omega

/-! ## The invoke step: code 0 writes exactly the data byte -/

theorem readU64_congr (m m' : Mem) (a b : Nat) (h : ∀ i, i < 8 → m (a + i) % 256 = m' (b + i) % 256) :
    readU64 m a = readU64 m' b := by
  rw [readU64_of_bytes m a (fun i => m' (b + i) % 256) h]
  exact (readU64_of_bytes m' b (fun i => m' (b + i) % 256) (fun _ _ => rfl)).symm

/-- A u64 written back over its own (byte-bounded) bytes changes nothing. -/
theorem writeU64_readback (m m' : Mem) (addr v a : Nat) (hv : ∀ j, j < 8 → v / 256 ^ j % 256 = m (addr + j) % 256)
    (hb : ∀ j, j < 8 → m (addr + j) < 256) (ha : addr ≤ a ∧ a < addr + 8) :
    (writeU64 m' addr v) a = m a := by
  obtain ⟨j, rfl⟩ : ∃ j, a = addr + j := ⟨a - addr, by omega⟩
  rw [writeU64_read_in _ _ _ _ (by omega), hv _ (by omega), Nat.mod_eq_of_lt (hb _ (by omega))]

theorem writeU8_read (m : Mem) (addr v a : Nat) :
    (writeU8 m addr v) a = if a = addr then v % 256 else m a := by
  show Mem.read (Mem.put m addr v) a = _
  rw [Mem.read_put]

/-- The runner's invoke step at the writer's invoke: when it returns code 0,
    caller memory differs from `s.mem` exactly at `base + 96`, which holds 42. -/
theorem writer_step {base : Nat} {s : State} (h : writerInv base s) (fuel' : Nat)
    (h0 : (stepCpi writerRegistry (executeFnCpiWithFuel writerRegistry) s fuel'
      (.call .sol_invoke_signed_c)).regs.r0 = 0) (a : Nat) :
    (stepCpi writerRegistry (executeFnCpiWithFuel writerRegistry) s fuel'
      (.call .sol_invoke_signed_c)).mem a = if a = base + 96 then 42 else s.mem a := by
  obtain ⟨elf, insns, subS, slots, hreg, hbuild, hc, hm⟩ :=
    Cpi.stepCpi_c_success _ _ s fuel' (writer_nativeNone h) h0
  rw [writer_registry h, Option.some.injEq] at hreg
  subst hreg
  rw [writer_accts h, buildCalleeVM_callee, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hbuild
  obtain ⟨rfl, rfl, rfl⟩ := hbuild
  rw [hm]
  generalize hpidB : readMemBytes s.mem (readU64 s.mem s.regs.r1) 32 = pidB at hc ⊢
  generalize hix : Cpi.invokeIxData s .sol_invoke_signed_c = ix at hc ⊢
  generalize hsf : executeFnCpiWithFuel writerRegistry (fetchFromArray calleeInsns)
    (calleeSubS s fuel' pidB (buildCpiSubInputN (buildAcctSlots [writerAcct s]) pidB ix)) fuel' = sfr
    at hc ⊢
  obtain ⟨sf, f⟩ := sfr
  simp only at hc ⊢
  rw [buildAcctSlots_single] at hc ⊢
  obtain ⟨hsf0, hcommit⟩ := commitCallee_single_ok s.mem (writerAcct s) sf f rfl hc
  -- The sub-input is long enough for the callee's store.
  have hsz : (writerAcct s).key.size = 32 ∧ (writerAcct s).owner.size = 32 := by
    rw [writerAcct_key h, writerAcct_owner h]; exact ⟨readMemBytes_size _ _ _, readMemBytes_size _ _ _⟩
  have hds : (writerAcct s).data.size = 2 := by rw [writerAcct_data h]; exact readMemBytes_size _ _ _
  have hge := emitNonDupBlock_size_ge (writerAcct s) hsz
  have hlen := (buildCpiSubInputN_single_get! (writerAcct s) pidB ix 89
    (by simp only [CPI_BLOCK_DATA_OFFSET] at hge; omega)).1
  have hrun := callee_run writerRegistry s fuel' pidB
    (buildCpiSubInputN (buildAcctSlots [writerAcct s]) pidB ix)
    (by rw [buildAcctSlots_single]; exact Nat.le_of_lt hlen)
  rw [hsf] at hrun
  have hsfm := hrun hsf0
  -- The callee's final memory over the account's sub-input bytes.
  have hM : ∀ k, 48 ≤ k → k < 98 →
      sf.mem (INPUT_START + k) = if k = 96 then 42 else s.mem (base + k) % 256 := by
    intro k hk1 hk2
    rw [hsfm, writeU8_read]
    by_cases hk : k = 96
    · subst hk; simp
    · rw [if_neg (by omega), if_neg hk]
      exact writer_subInput_mirror h pidB ix k hk1 hk2
  -- The post-call length (2) and lamports are the caller's.
  have hpost : readU64 sf.mem (INPUT_START + 8 + CPI_BLOCK_DATALEN_OFFSET) = 2 := by
    rw [← h.inputDataLen]
    apply readU64_congr
    intro i hi
    rw [show INPUT_START + 8 + CPI_BLOCK_DATALEN_OFFSET + i = INPUT_START + (88 + i) by
      simp only [CPI_BLOCK_DATALEN_OFFSET]; omega, hM _ (by omega) (by omega), if_neg (by omega),
      Nat.mod_mod, Nat.add_assoc]
  have hlam : readU64 sf.mem (INPUT_START + 8 + CPI_BLOCK_LAMPORTS_OFFSET) =
      readU64 s.mem (base + 80) := by
    apply readU64_congr
    intro i hi
    rw [show INPUT_START + 8 + CPI_BLOCK_LAMPORTS_OFFSET + i = INPUT_START + (80 + i) by
      simp only [CPI_BLOCK_LAMPORTS_OFFSET]; omega, hM _ (by omega) (by omega), if_neg (by omega),
      Nat.mod_mod, Nat.add_assoc]
  have hbase := h.base_ge
  rw [hcommit, hpost, hlam, writerAcct_dataPtr h, writerAcct_dataLenRefAddr,
    writerAcct_lamportsRefAddr h, writerAcct_ownerPtr h]
  -- Owner bytes.
  rw [loadBytesAt_read, readMemBytes_size]
  by_cases hA : base + 48 ≤ a ∧ a < base + 48 + 32
  · rw [if_pos hA, readMemBytes_get! _ _ _ _ (by omega), toUInt8_toNat_mod, Nat.mod_mod,
      show INPUT_START + 8 + CPI_BLOCK_OWNER_OFFSET + (a - (base + 48)) = INPUT_START + (a - base) by
        simp only [CPI_BLOCK_OWNER_OFFSET]; omega,
      hM _ (by omega) (by omega), if_neg (by omega), Nat.mod_mod,
      show base + (a - base) = a by omega, Nat.mod_eq_of_lt (h.inputBytes a (by omega) (by omega)),
      if_neg (by omega)]
  rw [if_neg hA]
  -- Lamports.
  by_cases hB : base + 80 ≤ a ∧ a < base + 80 + 8
  · rw [writeU64_readback s.mem _ _ _ _ (fun j hj => readU64_digit _ _ _ hj)
      (fun j hj => h.inputBytes _ (by omega) (by omega)) hB, if_neg (by omega)]
  rw [writeU64_read_outside _ _ _ _ hB]
  -- The input's data_len slot.
  by_cases hC : base + 96 - 8 ≤ a ∧ a < base + 96 - 8 + 8
  · rw [writeU64_readback s.mem _ _ _ _ (fun j hj => by
        rw [← h.inputDataLen, readU64_digit _ _ _ hj, show base + 96 - 8 = base + 88 by omega])
      (fun j hj => h.inputBytes _ (by omega) (by omega)) hC, if_neg (by omega)]
  rw [writeU64_read_outside _ _ _ _ hC]
  -- The account info's data_len slot.
  by_cases hD : 12884901968 ≤ a ∧ a < 12884901968 + 8
  · rw [writeU64_readback s.mem _ _ _ _ (fun j hj => by rw [← h.aiDataLen, readU64_digit _ _ _ hj])
      (fun j hj => h.lenBytes _ (by omega) (by omega)) hD, if_neg (by omega)]
  rw [writeU64_read_outside _ _ _ _ hD]
  -- Data bytes.
  rw [loadBytesAt_read, readMemBytes_size]
  by_cases hE : base + 96 ≤ a ∧ a < base + 96 + 2
  · rw [if_pos hE, readMemBytes_get! _ _ _ _ (by omega), toUInt8_toNat_mod, Nat.mod_mod,
      show INPUT_START + 8 + CPI_BLOCK_DATA_OFFSET + (a - (base + 96)) = INPUT_START + (a - base) by
        simp only [CPI_BLOCK_DATA_OFFSET]; omega,
      hM _ (by omega) (by omega)]
    by_cases ha : a = base + 96
    · rw [if_pos (by omega), if_pos ha]
    · rw [if_neg (by omega), if_neg ha, Nat.mod_mod, show base + (a - base) = a by omega,
        Nat.mod_eq_of_lt (h.inputBytes a (by omega) (by omega))]
  rw [if_neg hE, if_neg (by omega)]

/-! ## The contract -/

/-- A successful result of the restricted runner callee is the invoke step's
    memory, and the step returned code 0. -/
theorem writer_result {base : Nat} {s : State} {r : Cpi.CalleeResult}
    (hr : Cpi.restrict (Cpi.runnerCallee writerRegistry .sol_invoke_signed_c) (writerInv base) s r)
    (hc : r.code = 0) (a : Nat) : r.mem a = if a = base + 96 then 42 else s.mem a := by
  obtain ⟨hinv, fuel', hr⟩ := hr
  have h0 := congrArg (fun t => t.regs.r0) hr
  have hm := congrArg (fun t => t.mem a) hr
  simp only [chargeCu, Cpi.applyResult_r0, hc] at h0
  simp only [chargeCu, Cpi.applyResult, hc, if_true] at hm
  rw [← hm]
  exact writer_step hinv fuel' h0 a

theorem effectiveAddr_96 (base : Nat) : effectiveAddr base 96 = base + 96 := by
  unfold effectiveAddr; omega

/-- The writer callee, as the runner runs it from the writer's invoke, changes
    caller memory only at the account's first data byte. -/
theorem writer_callee_contract (baseAddr : Nat) :
    Cpi.writesOnly
      (Cpi.restrict (Cpi.runnerCallee writerRegistry .sol_invoke_signed_c) (writerInv baseAddr))
      [effectiveAddr baseAddr 96] := by
  intro s r hr hc a ha
  rw [writer_result hr hc a, if_neg]
  rw [← effectiveAddr_96]
  simpa using ha

/-- On success that byte is 42. -/
theorem writer_callee_value (baseAddr : Nat) :
    ∀ s r, Cpi.restrict (Cpi.runnerCallee writerRegistry .sol_invoke_signed_c)
        (writerInv baseAddr) s r →
      r.code = 0 → r.mem (effectiveAddr baseAddr 96) = 42 := by
  intro s r hr hc
  rw [writer_result hr hc, effectiveAddr_96, if_pos rfl]

/-! ## The callee succeeds from the writer's invoke

With enough fuel the runner's invoke step at a `writerInv` state takes the
BPF arm, the callee runs its four instructions to `exit` with code 0 and
four CU, and the write-back commits (the account's length stays 2, inside
the realloc bound). -/

/-- The callee runs to its exit: code 0, four CU, the store of 42. -/
theorem callee_exec_ok (t : State) (n : Nat) (hpc : t.pc = 0) (hex : t.exitCode = none)
    (hcu : t.cuConsumed = 0) (hbud : 3 ≤ t.cuBudget) (hcs : t.callStack = [])
    (hr1 : t.regs.r1 = INPUT_START)
    (hreg : t.regions.containsWritable (INPUT_START + 96) 1 = true) :
    (executeFn (fetchFromArray calleeInsns) t (n + 4)).exitCode = some 0 ∧
    (executeFn (fetchFromArray calleeInsns) t (n + 4)).cuConsumed = 4 ∧
    (executeFn (fetchFromArray calleeInsns) t (n + 4)).mem =
      writeU8 t.mem (INPUT_START + 96) 42 := by
  have hf0 : fetchFromArray calleeInsns 0 = some (.mov64 .r2 (.imm 42)) := rfl
  have hf1 : fetchFromArray calleeInsns 1 = some (.stx .byte .r1 96 .r2) := rfl
  have hf2 : fetchFromArray calleeInsns 2 = some (.mov64 .r0 (.imm 0)) := rfl
  have hf3 : fetchFromArray calleeInsns 3 = some .exit := rfl
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
  have hcu4 : (chargeCu (step .exit t3)).cuConsumed = 4 := by
    simp [s3, c3]
  have hm4 : (chargeCu (step .exit t3)).mem = writeU8 t.mem (INPUT_START + 96) 42 := by
    simp [s3, m3]
  rw [executeFn_step _ t (n + 3) _ hex (by omega) (hpc ▸ hf0), ht1,
    executeFn_step _ t1 (n + 2) _ x1 (by omega) (p1 ▸ hf1), ht2,
    executeFn_step _ t2 (n + 1) _ x2 (by omega) (p2 ▸ hf2), ht3,
    executeFn_step _ t3 n _ x3 (by omega) (p3 ▸ hf3),
    executeFn_halted _ _ n 0 hex4]
  exact ⟨hex4, hcu4, hm4⟩

/-- The runner's sub-run of the callee with at least four fuel units exits
    with code 0 after four CU, having stored 42 at `INPUT_START + 96`.
    Stated over an arbitrary sub-input: bridging the CPI-aware run to
    `executeFn` on the concrete serialized input instead makes the kernel
    evaluate the run. -/
theorem callee_run_ok (registry : Nat → Option ByteArray) (s : State) (n : Nat)
    (pidB subInput : ByteArray) (hsz : 97 ≤ subInput.size) :
    (executeFnCpiWithFuel registry (fetchFromArray calleeInsns)
      (calleeSubS s (n + 4) pidB subInput) (n + 4)).1.exitCode = some 0 ∧
    (executeFnCpiWithFuel registry (fetchFromArray calleeInsns)
      (calleeSubS s (n + 4) pidB subInput) (n + 4)).1.cuConsumed = 4 ∧
    (executeFnCpiWithFuel registry (fetchFromArray calleeInsns)
      (calleeSubS s (n + 4) pidB subInput) (n + 4)).1.mem =
        writeU8 (calleeSubS s (n + 4) pidB subInput).mem (INPUT_START + 96) 42 := by
  have hb := executeFnCpi_eq_executeFn_of_no_cpi_array registry calleeInsns
    (calleeSubS s (n + 4) pidB subInput) (n + 4) (by decide)
  unfold executeFnCpi at hb
  rw [hb]
  exact callee_exec_ok _ n rfl rfl rfl (by simp [calleeSubS]) rfl rfl
    (calleeRegions_writable _ hsz)

/-- A successful callee run with the writer's single-byte store commits its
    exit code and compute usage without a realloc violation. -/
theorem writer_bpfResult_ok {base : Nat} {s : State} (h : writerInv base s)
    (fuel : Nat) (pidB ix : ByteArray) (run : State × Nat)
    (hx : run.1.exitCode = some 0) (hcu : run.1.cuConsumed = 4)
    (hm : run.1.mem = writeU8
      (calleeSubS s fuel pidB (buildCpiSubInputN (buildAcctSlots [writerAcct s]) pidB ix)).mem
      (INPUT_START + 96) 42) :
    (Cpi.bpfResult s.mem (buildAcctSlots [writerAcct s]) run).code = 0 ∧
      (Cpi.bpfResult s.mem (buildAcctSlots [writerAcct s]) run).cuConsumed = 4 := by
  rcases run with ⟨sf, f⟩
  have hM : ∀ k, 48 ≤ k → k < 98 →
      sf.mem (INPUT_START + k) = if k = 96 then 42 else s.mem (base + k) % 256 := by
    intro k hk1 hk2
    rw [hm, writeU8_read]
    by_cases hk : k = 96
    · subst hk; simp
    · rw [if_neg (by omega), if_neg hk]
      exact writer_subInput_mirror h pidB ix k hk1 hk2
  have hpost : readU64 sf.mem (INPUT_START + 8 + CPI_BLOCK_DATALEN_OFFSET) = 2 := by
    rw [← h.inputDataLen]
    apply readU64_congr
    intro i hi
    rw [show INPUT_START + 8 + CPI_BLOCK_DATALEN_OFFSET + i = INPUT_START + (88 + i) by
      simp only [CPI_BLOCK_DATALEN_OFFSET]; omega, hM _ (by omega) (by omega), if_neg (by omega),
      Nat.mod_mod, Nat.add_assoc]
  have hfst : (commitCallee s.mem [slot1 (writerAcct s)] sf f).1 = sf := by
    apply commitCallee_single_fst _ _ _ _ writerAcct_isWritable
    rw [hpost, writerAcct_dataLen h]
    simp [MAX_PERMITTED_DATA_INCREASE]
  rw [buildAcctSlots_single, Cpi.bpfResult_code, Cpi.bpfResult_cuConsumed, hfst, hx, hcu]
  exact ⟨rfl, rfl⟩

/-- The runner's invoke step at a `writerInv` state with at least four fuel
    units commits a code-0 result of four CU. -/
theorem writer_step_ok {base : Nat} {s : State} (h : writerInv base s) (fuel' : Nat)
    (hf : 4 ≤ fuel') :
    ∃ r0 : Cpi.CalleeResult,
      stepCpi writerRegistry (executeFnCpiWithFuel writerRegistry) s fuel'
          (.call .sol_invoke_signed_c) = Cpi.applyResult s r0 ∧
        r0.code = 0 ∧ r0.cuConsumed = 4 := by
  have hbuild := buildCalleeVM_callee s fuel'
    (readMemBytes s.mem (readU64 s.mem s.regs.r1) 32) (Cpi.invokeAccts s .sol_invoke_signed_c)
    (Cpi.invokeIxData s .sol_invoke_signed_c)
  rw [Cpi.stepCpi_c_bpf writerRegistry _ s fuel' (writerAcct s) calleeElf _ _ _
    (by rw [h.depth]; omega) (writer_accts h) (writer_nativeNone h) (writer_registry h) hbuild]
  generalize readMemBytes s.mem (readU64 s.mem s.regs.r1) 32 = pidB
  generalize Cpi.invokeIxData s .sol_invoke_signed_c = ix
  rw [writer_accts h]
  -- The sub-input is long enough for the callee's store.
  have hsz : (writerAcct s).key.size = 32 ∧ (writerAcct s).owner.size = 32 := by
    rw [writerAcct_key h, writerAcct_owner h]
    exact ⟨readMemBytes_size _ _ _, readMemBytes_size _ _ _⟩
  have hds : (writerAcct s).data.size = 2 := by
    rw [writerAcct_data h]; exact readMemBytes_size _ _ _
  have hge := emitNonDupBlock_size_ge (writerAcct s) hsz
  have hlen := (buildCpiSubInputN_single_get! (writerAcct s) pidB ix 89
    (by simp only [CPI_BLOCK_DATA_OFFSET] at hge; omega)).1
  have hsz97 : 97 ≤ (buildCpiSubInputN (buildAcctSlots [writerAcct s]) pidB ix).size := by
    rw [buildAcctSlots_single]; exact Nat.le_of_lt hlen
  -- The callee's run.
  obtain ⟨n, rfl⟩ : ∃ n, fuel' = n + 4 := ⟨fuel' - 4, by omega⟩
  obtain ⟨hx0, hc4, hm⟩ := callee_run_ok writerRegistry s n pidB
    (buildCpiSubInputN (buildAcctSlots [writerAcct s]) pidB ix) hsz97
  have hok := writer_bpfResult_ok h (n + 4) pidB ix _ hx0 hc4 hm
  exact ⟨_, rfl, hok.1, hok.2⟩

/-! ## The caller's path, restated

The code, precondition and region side conditions of
`Sbpfv3CpiWriterLiftedSuccess_cpi_path`, named so the end-to-end statement
can refer to them. -/

/-- The writer's prefix code (pcs 0 to 45). -/
def writerCr1 : CodeReq :=
  (((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r6 (.reg .r1))).union
    (CodeReq.singleton 1 (.add64 .r1 (.imm (10360))))).union
    (CodeReq.singleton 2 (.lddw .r2 (12884901888)))).union
    (CodeReq.singleton 3 (.stx .dword .r2 0 .r1))).union
    (CodeReq.singleton 4 (.lddw .r1 (12884901896)))).union
    (CodeReq.singleton 5 (.lddw .r2 (12884901936)))).union
    (CodeReq.singleton 6 (.stx .dword .r1 0 .r2))).union
    (CodeReq.singleton 7 (.lddw .r1 (12884901904)))).union
    (CodeReq.singleton 8 (.st .dword .r1 0 (1)))).union
    (CodeReq.singleton 9 (.lddw .r1 (12884901912)))).union
    (CodeReq.singleton 10 (.lddw .r3 (12884902008)))).union
    (CodeReq.singleton 11 (.stx .dword .r1 0 .r3))).union
    (CodeReq.singleton 12 (.lddw .r1 (12884901920)))).union
    (CodeReq.singleton 13 (.st .dword .r1 0 (0)))).union
    (CodeReq.singleton 14 (.mov64 .r1 (.reg .r6)))).union
    (CodeReq.singleton 15 (.add64 .r1 (.imm (16))))).union
    (CodeReq.singleton 16 (.stx .dword .r2 0 .r1))).union
    (CodeReq.singleton 17 (.lddw .r2 (12884901944)))).union
    (CodeReq.singleton 18 (.st .dword .r2 0 (1)))).union
    (CodeReq.singleton 19 (.lddw .r2 (12884901952)))).union
    (CodeReq.singleton 20 (.stx .dword .r2 0 .r1))).union
    (CodeReq.singleton 21 (.mov64 .r1 (.reg .r6)))).union
    (CodeReq.singleton 22 (.add64 .r1 (.imm (80))))).union
    (CodeReq.singleton 23 (.lddw .r2 (12884901960)))).union
    (CodeReq.singleton 24 (.stx .dword .r2 0 .r1))).union
    (CodeReq.singleton 25 (.lddw .r1 (12884901968)))).union
    (CodeReq.singleton 26 (.st .dword .r1 0 (2)))).union
    (CodeReq.singleton 27 (.mov64 .r1 (.reg .r6)))).union
    (CodeReq.singleton 28 (.add64 .r1 (.imm (96))))).union
    (CodeReq.singleton 29 (.lddw .r2 (12884901976)))).union
    (CodeReq.singleton 30 (.stx .dword .r2 0 .r1))).union
    (CodeReq.singleton 31 (.mov64 .r1 (.reg .r6)))).union
    (CodeReq.singleton 32 (.add64 .r1 (.imm (48))))).union
    (CodeReq.singleton 33 (.lddw .r2 (12884901984)))).union
    (CodeReq.singleton 34 (.stx .dword .r2 0 .r1))).union
    (CodeReq.singleton 35 (.lddw .r1 (12884901992)))).union
    (CodeReq.singleton 36 (.ldx .dword .r2 .r6 10344))).union
    (CodeReq.singleton 37 (.stx .dword .r1 0 .r2))).union
    (CodeReq.singleton 38 (.lddw .r1 (12884902000)))).union
    (CodeReq.singleton 39 (.st .dword .r1 0 (256)))).union
    (CodeReq.singleton 40 (.mov64 .r7 (.imm (0))))).union
    (CodeReq.singleton 41 (.lddw .r1 (12884901888)))).union
    (CodeReq.singleton 42 (.lddw .r2 (12884901952)))).union
    (CodeReq.singleton 43 (.mov64 .r3 (.imm (1))))).union
    (CodeReq.singleton 44 (.mov64 .r4 (.reg .r6)))).union
    (CodeReq.singleton 45 (.mov64 .r5 (.imm (0))))))

/-- The writer's success suffix code (pcs 47 to 55). -/
def writerCr2 : CodeReq :=
  (((((((CodeReq.singleton 47 (.jeq .r0 (.imm (0)) 51)).union
    (CodeReq.singleton 51 (.ldx .byte .r1 .r6 96))).union
    (CodeReq.singleton 52 (.add64 .r1 (.imm (1))))).union
    (CodeReq.singleton 53 (.lddw .r2 (12884902088)))).union
    (CodeReq.singleton 54 (.stx .byte .r2 0 .r1))).union
    (CodeReq.singleton 55 (.mov64 .r0 (.reg .r7)))))

/-- The writer's precondition at entry. -/
def writerPre (baseAddr vR6Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3 oldMemD_4
    oldMemD_5 oldMemD_6 oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13
    oldMemD_14 vR7Old vR4Old vR5Old : Nat) (cpiRdOld : ByteArray)
    (cpiR0Old cpiFpOld0 cpi_oldMemB_1 : Nat) : Assertion :=
  ((.r1 ↦ᵣ baseAddr) **
  (.r6 ↦ᵣ vR6Old) **
  (.r2 ↦ᵣ vR2Old) **
  (effectiveAddr (toU64 12884901888) 0 ↦U64 oldMemD_0) **
  (effectiveAddr (toU64 12884901896) 0 ↦U64 oldMemD_1) **
  (effectiveAddr (toU64 12884901904) 0 ↦U64 oldMemD_2) **
  (.r3 ↦ᵣ vR3Old) **
  (effectiveAddr (toU64 12884901912) 0 ↦U64 oldMemD_3) **
  (effectiveAddr (toU64 12884901920) 0 ↦U64 oldMemD_4) **
  (effectiveAddr (toU64 12884901936) 0 ↦U64 oldMemD_5) **
  (effectiveAddr (toU64 12884901944) 0 ↦U64 oldMemD_6) **
  (effectiveAddr (toU64 12884901952) 0 ↦U64 oldMemD_7) **
  (effectiveAddr (toU64 12884901960) 0 ↦U64 oldMemD_8) **
  (effectiveAddr (toU64 12884901968) 0 ↦U64 oldMemD_9) **
  (effectiveAddr (toU64 12884901976) 0 ↦U64 oldMemD_10) **
  (effectiveAddr (toU64 12884901984) 0 ↦U64 oldMemD_11) **
  (effectiveAddr baseAddr 10344 ↦U64 oldMemD_12) **
  (effectiveAddr (toU64 12884901992) 0 ↦U64 oldMemD_13) **
  (effectiveAddr (toU64 12884902000) 0 ↦U64 oldMemD_14) **
  (.r7 ↦ᵣ vR7Old) **
  (.r4 ↦ᵣ vR4Old) **
  (.r5 ↦ᵣ vR5Old) **
  (.r0 ↦ᵣ cpiR0Old) **
  (↦ReturnData cpiRdOld) **
  (effectiveAddr baseAddr 96 ↦ₘ cpiFpOld0) **
  (effectiveAddr (toU64 12884902088) 0 ↦ₘ cpi_oldMemB_1))

/-- The prefix's region side condition. -/
def writerRr1 (baseAddr : Nat) : RegionTable → Prop :=
  (fun rt => ((((((((((((((rt.containsWritable (effectiveAddr (toU64 12884901888) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901896) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901904) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901912) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901920) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901936) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901944) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901952) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901960) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901968) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901976) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901984) 0) 8 = true) ∧
              rt.containsRange (effectiveAddr baseAddr 10344) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884901992) 0) 8 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884902000) 0) 8 = true)

/-- The suffix's region side condition. -/
def writerRr2 (baseAddr : Nat) : RegionTable → Prop :=
  (fun rt => (rt.containsRange (effectiveAddr baseAddr 96) 1 = true) ∧
              rt.containsWritable (effectiveAddr (toU64 12884902088) 0) 1 = true)

/-! ## The caller's input as a frame

`writerInv` needs caller facts the prefix never touches: the account's key,
owner, lamports and length bytes (`[base + 16, base + 96)`), its second data
byte, the callee's id (the second account's key at `base + 10360`), and an
empty call stack (for the final `exit`). They ride through the prefix and
the suffix as the frame `writerFrame`. -/

/-- The caller input the invoke and the final `exit` rely on. -/
def writerFrame (base : Nat) (acct : ByteArray) (d1 : Nat) : Assertion :=
  (base + 16 ↦Bytes acct) ** (base + 97 ↦ₘ d1) ** (base + 10360 ↦Bytes writerCalleeId) **
    (↦CallStack [])

theorem writerFrame_pcFree (base : Nat) (acct : ByteArray) (d1 : Nat) :
    (writerFrame base acct d1).pcFree := by
  unfold writerFrame; sl_pcfree

/-- The prefix post (`Sbpfv3CpiWriterLifted_lifted_spec`) with the cells the
    CPI and the suffix own, reordered so the cells `writerInv` reads come
    first. -/
def writerMid (baseAddr oldMemD_12 : Nat) (cpiRdOld : ByteArray)
    (cpiR0Old cpiFpOld0 cpi_oldMemB_1 : Nat) : Assertion :=
  (.r1 ↦ᵣ toU64 12884901888) **
  (.r2 ↦ᵣ toU64 12884901952) **
  (.r5 ↦ᵣ toU64 0) **
  (effectiveAddr (toU64 12884901888) 0 ↦U64 wrapAdd baseAddr (toU64 10360)) **
  (effectiveAddr (toU64 12884901904) 0 ↦U64 toU64 1 % 2 ^ (8 * 8)) **
  (effectiveAddr (toU64 12884901920) 0 ↦U64 toU64 0 % 2 ^ (8 * 8)) **
  (effectiveAddr (toU64 12884901952) 0 ↦U64 wrapAdd baseAddr (toU64 16)) **
  (effectiveAddr (toU64 12884901960) 0 ↦U64 wrapAdd baseAddr (toU64 80)) **
  (effectiveAddr (toU64 12884901968) 0 ↦U64 toU64 2 % 2 ^ (8 * 8)) **
  (effectiveAddr (toU64 12884901976) 0 ↦U64 wrapAdd baseAddr (toU64 96)) **
  (effectiveAddr (toU64 12884901984) 0 ↦U64 wrapAdd baseAddr (toU64 48)) **
  (effectiveAddr (toU64 12884902000) 0 ↦U64 toU64 256 % 2 ^ (8 * 8)) **
  (effectiveAddr baseAddr 96 ↦ₘ cpiFpOld0) **
  (.r6 ↦ᵣ baseAddr) **
  (effectiveAddr (toU64 12884901896) 0 ↦U64 toU64 12884901936) **
  (.r3 ↦ᵣ toU64 1) **
  (effectiveAddr (toU64 12884901912) 0 ↦U64 toU64 12884902008) **
  (effectiveAddr (toU64 12884901936) 0 ↦U64 wrapAdd baseAddr (toU64 16)) **
  (effectiveAddr (toU64 12884901944) 0 ↦U64 toU64 1 % 2 ^ (8 * 8)) **
  (effectiveAddr baseAddr 10344 ↦U64 oldMemD_12) **
  (effectiveAddr (toU64 12884901992) 0 ↦U64 oldMemD_12) **
  (.r7 ↦ᵣ toU64 0) **
  (.r4 ↦ᵣ baseAddr) **
  (.r0 ↦ᵣ cpiR0Old) **
  (↦ReturnData cpiRdOld) **
  (effectiveAddr (toU64 12884902088) 0 ↦ₘ cpi_oldMemB_1)

/-- The writer's prefix, framed with the CPI's and the suffix's cells, ends
    in `writerMid`. -/
theorem writer_prefix (baseAddr vR6Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3
    oldMemD_4 oldMemD_5 oldMemD_6 oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12
    oldMemD_13 oldMemD_14 vR7Old vR4Old vR5Old : Nat) (holdMemD_12_lt : oldMemD_12 < 2 ^ 64)
    (cpiRdOld : ByteArray) (cpiR0Old cpiFpOld0 cpi_oldMemB_1 : Nat) :
    cuTripleWithinMem 46 0 0 46 writerCr1
      (writerPre baseAddr vR6Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3 oldMemD_4
        oldMemD_5 oldMemD_6 oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12
        oldMemD_13 oldMemD_14 vR7Old vR4Old vR5Old cpiRdOld cpiR0Old cpiFpOld0 cpi_oldMemB_1)
      (writerMid baseAddr oldMemD_12 cpiRdOld cpiR0Old cpiFpOld0 cpi_oldMemB_1)
      (writerRr1 baseAddr) := by
  have h := cuTripleWithinMem_frame_right ((.r0 ↦ᵣ cpiR0Old) **
      (↦ReturnData cpiRdOld) **
      (effectiveAddr baseAddr 96 ↦ₘ cpiFpOld0) **
      (effectiveAddr (toU64 12884902088) 0 ↦ₘ cpi_oldMemB_1)) (by sl_pcfree)
    (Examples.Lifted.Sbpfv3CpiWriterLifted.Sbpfv3CpiWriterLifted_lifted_spec baseAddr vR6Old
      vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3 oldMemD_4 oldMemD_5 oldMemD_6
      oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 oldMemD_14 vR7Old
      vR4Old vR5Old holdMemD_12_lt)
  unfold writerPre writerMid writerCr1 writerRr1
  sl_exact h

/-! ### Reading assertion cells -/

section Cells
variable {s : State}

theorem hl {P Q : Assertion} (h : (P ** Q).holdsFor s) : P.holdsFor s :=
  holdsFor_sepConj_left h

theorem hr {P Q : Assertion} (h : (P ** Q).holdsFor s) : Q.holdsFor s :=
  holdsFor_sepConj_right h

theorem reg_of_holds {r : Reg} {v : Nat} (h : (r ↦ᵣ v).holdsFor s) : s.regs.get r = v := by
  obtain ⟨hh, hc, heq⟩ := h
  have heq' : hh = PartialState.singletonReg r v := heq
  subst heq'
  exact hc.regs r v (by simp [PartialState.singletonReg])

theorem callStack_of_holds {cs : List CallFrame} (h : (↦CallStack cs).holdsFor s) :
    s.callStack = cs := by
  obtain ⟨hh, hc, heq⟩ := h
  have heq' : hh = PartialState.singletonCallStack cs := heq
  subst heq'
  exact hc.callStack cs rfl

theorem bytes_of_holds {a : Nat} {bs : ByteArray} (h : (a ↦Bytes bs).holdsFor s) :
    ∀ i, i < bs.size → s.mem (a + i) = (bs.get! i).toNat := by
  obtain ⟨hh, hc, heq⟩ := h
  have heq' : hh = PartialState.singletonMemBytes a bs := heq
  subst heq'
  intro i hi
  exact hc.mem _ _ (PartialState.singletonMemBytes_mem_at a bs i hi)

theorem u64byte_of_holds {a v : Nat} (h : (a ↦U64 v).holdsFor s) :
    ∀ i, i < 8 → s.mem (a + i) = v / 256 ^ i % 256 := by
  obtain ⟨hh, hc, heq⟩ := h
  have heq' : hh = PartialState.singletonMemU64 a v := heq
  subst heq'
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · simpa using hc.mem a _ (PartialState.singletonMemU64_mem_0 a v)
  · exact hc.mem _ _ (PartialState.singletonMemU64_mem_1 a v)
  · exact hc.mem _ _ (PartialState.singletonMemU64_mem_2 a v)
  · exact hc.mem _ _ (PartialState.singletonMemU64_mem_3 a v)
  · exact hc.mem _ _ (PartialState.singletonMemU64_mem_4 a v)
  · exact hc.mem _ _ (PartialState.singletonMemU64_mem_5 a v)
  · exact hc.mem _ _ (PartialState.singletonMemU64_mem_6 a v)
  · exact hc.mem _ _ (PartialState.singletonMemU64_mem_7 a v)
  · omega

end Cells

theorem readMemBytes_congr (m m' : Mem) (a n : Nat) (h : ∀ i, i < n → m (a + i) = m' (a + i)) :
    readMemBytes m a n = readMemBytes m' a n := by
  unfold readMemBytes
  congr 1
  have aux (xs : List Nat) (acc : Array UInt8)
      (hx : ∀ i ∈ xs, m (a + i) = m' (a + i)) :
      xs.foldl (fun acc i => acc.push ((m (a + i)) % 256).toUInt8) acc =
      xs.foldl (fun acc i => acc.push ((m' (a + i)) % 256).toUInt8) acc := by
    induction xs generalizing acc with
    | nil => rfl
    | cons i is ih =>
      simp only [List.foldl_cons]
      rw [hx i (by simp)]
      exact ih _ (by
        intro j hj
        exact hx j (by simp [hj]))
  exact aux (List.range n) #[] (fun i hi => h i (List.mem_range.mp hi))

/-- The invariant at the invoke, from the prefix post and the frame. -/
theorem writerInv_of_mid {baseAddr oldMemD_12 cpiR0Old cpiFpOld0 cpi_oldMemB_1 d1 : Nat}
    {cpiRdOld acct : ByteArray} {sI : State}
    (hbase : 12884901888 + 88 ≤ baseAddr) (hbase' : baseAddr + 10360 < 2 ^ 64)
    (hacct : acct.size = 80)
    (hacctLen : ∀ i, i < 8 → (acct.get! (72 + i)).toNat = if i = 0 then 2 else 0)
    (hfp : cpiFpOld0 < 256) (hd1 : d1 < 256)
    (hQ : (writerMid baseAddr oldMemD_12 cpiRdOld cpiR0Old cpiFpOld0 cpi_oldMemB_1 **
      writerFrame baseAddr acct d1).holdsFor sI)
    (hdepth : sI.invokeDepth = 0)
    (hpriv : sI.origPrivs.any
      (fun t => t.1 == readMemBytes sI.mem (baseAddr + 16) 32 && t.2.2) = true) :
    writerInv baseAddr sI := by
  have hM := hl hQ
  have hW := hr hQ
  unfold writerMid at hM
  unfold writerFrame at hW
  have hAcct := bytes_of_holds (hl hW)
  have hD1 := mem_of_holdsFor_memByteIs (hl (hr hW))
  have hId := bytes_of_holds (hl (hr (hr hW)))
  have hFp := mem_of_holdsFor_memByteIs (hl (hr (hr (hr (hr (hr (hr (hr (hr (hr (hr (hr (hr hM)))))))))))))
  have wa : ∀ k : Nat, k ≤ 10360 → wrapAdd baseAddr (toU64 (k : Int)) = baseAddr + k :=
    fun k hk => wrapAdd_const_of_lt (by omega)
  have rd : ∀ {a v : Nat}, (a ↦U64 v).holdsFor sI → readU64 sI.mem a = v % 2 ^ 64 :=
    fun h => readU64_of_holdsFor_memU64Is h
  refine
    { base_ge := hbase
      r1 := by simpa using reg_of_holds (hl hM)
      r2 := by simpa using reg_of_holds (hl (hr hM))
      r5 := by simpa using reg_of_holds (hl (hr (hr hM)))
      depth := hdepth
      ixProgId := by
        rw [show (12884901888 : Nat) = effectiveAddr (toU64 12884901888) 0 from rfl,
          rd (hl (hr (hr (hr hM)))), show (10360 : Int) = ((10360 : Nat) : Int) from rfl,
          wa 10360 (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      ixAcctCount := by
        rw [show (12884901904 : Nat) = effectiveAddr (toU64 12884901904) 0 from rfl,
          rd (hl (hr (hr (hr (hr hM)))))]; rfl
      ixDataLen := by
        rw [show (12884901920 : Nat) = effectiveAddr (toU64 12884901920) 0 from rfl,
          rd (hl (hr (hr (hr (hr (hr hM))))))]; rfl
      aiKey := by
        rw [show (12884901952 : Nat) = effectiveAddr (toU64 12884901952) 0 from rfl,
          rd (hl (hr (hr (hr (hr (hr (hr hM))))))), show (16 : Int) = ((16 : Nat) : Int) from rfl,
          wa 16 (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      aiLamports := by
        rw [show (12884901960 : Nat) = effectiveAddr (toU64 12884901960) 0 from rfl,
          rd (hl (hr (hr (hr (hr (hr (hr (hr hM)))))))),
          show (80 : Int) = ((80 : Nat) : Int) from rfl, wa 80 (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      aiDataLen := by
        rw [show (12884901968 : Nat) = effectiveAddr (toU64 12884901968) 0 from rfl,
          rd (hl (hr (hr (hr (hr (hr (hr (hr (hr hM)))))))))]; rfl
      aiData := by
        rw [show (12884901976 : Nat) = effectiveAddr (toU64 12884901976) 0 from rfl,
          rd (hl (hr (hr (hr (hr (hr (hr (hr (hr (hr hM)))))))))),
          show (96 : Int) = ((96 : Nat) : Int) from rfl, wa 96 (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      aiOwner := by
        rw [show (12884901984 : Nat) = effectiveAddr (toU64 12884901984) 0 from rfl,
          rd (hl (hr (hr (hr (hr (hr (hr (hr (hr (hr (hr hM))))))))))),
          show (48 : Int) = ((48 : Nat) : Int) from rfl, wa 48 (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      aiWritable := by
        have := u64byte_of_holds (hl (hr (hr (hr (hr (hr (hr (hr (hr (hr (hr (hr hM)))))))))))) 1
          (by omega)
        rw [show (12884902001 : Nat) = effectiveAddr (toU64 12884902000) 0 + 1 from rfl, this]
        decide
      progId := by
        intro i hi
        exact hId i (by rw [show writerCalleeId.size = 32 from rfl]; exact hi)
      origWritable := hpriv
      inputDataLen := by
        rw [readU64_of_bytes sI.mem (baseAddr + 88) (fun i => if i = 0 then 2 else 0)]
        · rfl
        · intro i hi
          rw [show baseAddr + 88 + i = baseAddr + 16 + (72 + i) by omega,
            hAcct _ (by omega), hacctLen i hi]
          split <;> rfl
      inputBytes := by
        intro a ha1 ha2
        by_cases h96 : a < baseAddr + 96
        · rw [show a = baseAddr + 16 + (a - (baseAddr + 16)) by omega, hAcct _ (by omega)]
          exact UInt8.toNat_lt _
        · by_cases h97 : a = baseAddr + 96
          · subst h97; rw [← effectiveAddr_96, hFp]; exact hfp
          · rw [show a = baseAddr + 97 by omega, hD1]; exact hd1
      lenBytes := by
        intro a ha1 ha2
        have := u64byte_of_holds (hl (hr (hr (hr (hr (hr (hr (hr (hr hM)))))))))
          (a - 12884901968) (by omega)
        rw [show effectiveAddr (toU64 12884901968) 0 + (a - 12884901968) = a by
          simp [effectiveAddr]; omega] at this
        rw [this]; exact Nat.mod_lt _ (by omega) }

/-! ## End to end -/

/-- A halted runner state is a fixed point. -/
theorem executeFnCpiWithFuel_halted (registry : Nat → Option ByteArray)
    (fetch : Nat → Option Insn) (t : State) (c n : Nat) (h : t.exitCode = some c) :
    (executeFnCpiWithFuel registry fetch t n).1 = t := by
  cases n <;> simp [executeFnCpiWithFuel, h]

/-- The runner's last step at a live, in-budget `exit` with an empty call
    stack halts with `r0` as the exit code and memory unchanged. -/
theorem runner_exit (registry : Nat → Option ByteArray) (fetch : Nat → Option Insn)
    (t : State) (k : Nat) (hex : t.exitCode = none) (hbud : t.cuConsumed ≤ t.cuBudget)
    (hf : fetch t.pc = some .exit) (hcs : t.callStack = []) :
    (executeFnCpiWithFuel registry fetch t (k + 1)).1.exitCode = some t.regs.r0 ∧
      (executeFnCpiWithFuel registry fetch t (k + 1)).1.mem = t.mem := by
  rw [executeFnCpiWithFuel_succ_insn registry fetch t k _ hex (Nat.not_lt.mpr hbud) hf,
    Cpi.stepCpi_of_not_cpi _ _ _ _ _ rfl]
  have hx : (chargeCu (step .exit t)).exitCode = some t.regs.r0 := by simp [step, hcs]
  rw [executeFnCpiWithFuel_halted _ _ _ _ _ hx]
  exact ⟨hx, by simp [step, hcs]⟩

/-- **The writer and its callee, end to end.** The real runner, executing the
    writer caller (any fetch honoring its decoded code, `exit` at pc 56) with
    the pinned callee registered, from any entry state satisfying the
    caller's precondition, the input frame and the path's side conditions,
    reaches the exit at pc 56 with the account's first data byte 42 at
    `base + 96` and the marker 43 at `HEAP_START + 200`, then exits 0. The
    callee's success is proved, not assumed. -/
theorem writer_end_to_end
    (baseAddr vR6Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3 oldMemD_4 oldMemD_5
      oldMemD_6 oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13
      oldMemD_14 vR7Old vR4Old vR5Old : Nat) (holdMemD_12_lt : oldMemD_12 < 2 ^ 64)
    (cpiRdOld : ByteArray) (cpiR0Old cpiFpOld0 cpi_oldMemB_1 : Nat)
    (acct : ByteArray) (d1 : Nat)
    (hbase : 12884901888 + 88 ≤ baseAddr) (hbase' : baseAddr + 10360 < 2 ^ 64)
    (hacct : acct.size = 80)
    (hacctLen : ∀ i, i < 8 → (acct.get! (72 + i)).toNat = if i = 0 then 2 else 0)
    (hfp : cpiFpOld0 < 256) (hd1 : d1 < 256)
    (fetch : Nat → Option Insn)
    (hcr1 : (writerCr1.union (CodeReq.singleton 46 (.call .sol_invoke_signed_c))).SatisfiedBy
      fetch)
    (hcr2 : writerCr2.SatisfiedBy fetch) (hexit : fetch 56 = some .exit)
    (s : State)
    (hP : (writerPre baseAddr vR6Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3
      oldMemD_4 oldMemD_5 oldMemD_6 oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11
      oldMemD_12 oldMemD_13 oldMemD_14 vR7Old vR4Old vR5Old cpiRdOld cpiR0Old cpiFpOld0
      cpi_oldMemB_1 ** writerFrame baseAddr acct d1).holdsFor s)
    (hpc : s.pc = 0) (hex : s.exitCode = none)
    (hbud : s.cuConsumed + 46 + Cpi.cu + 5 + 6 ≤ s.cuBudget)
    (hrr1 : writerRr1 baseAddr s.regions) (hrr2 : writerRr2 baseAddr s.regions)
    (hdepth : s.invokeDepth = 0)
    (hpriv : s.origPrivs.any
      (fun t => t.1 == readMemBytes s.mem (baseAddr + 16) 32 && t.2.2) = true)
    (F : Nat) (hF : 46 + 1 + 6 + 1 ≤ F) :
    ∃ sE k, sE.pc = 56 ∧ sE.exitCode = none ∧ sE.regs.r0 = 0 ∧
      sE.mem (baseAddr + 96) = 42 ∧ sE.mem (HEAP_START + 200) = 43 ∧
      executeFnCpiWithFuel writerRegistry fetch s F =
        executeFnCpiWithFuel writerRegistry fetch sE (k + 1) ∧
      (executeFnCpiWithFuel writerRegistry fetch s F).1.exitCode = some 0 ∧
      (executeFnCpiWithFuel writerRegistry fetch s F).1.mem = sE.mem := by
  have hW := writerFrame_pcFree baseAddr acct d1
  -- The invoke state: the prefix post, framed by the input.
  obtain ⟨k0, _, hpc0, hex0, hcu0, hQ0⟩ :=
    writer_prefix baseAddr vR6Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3
      oldMemD_4 oldMemD_5 oldMemD_6 oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11
      oldMemD_12 oldMemD_13 oldMemD_14 vR7Old vR4Old vR5Old holdMemD_12_lt cpiRdOld cpiR0Old
      cpiFpOld0 cpi_oldMemB_1 (writerFrame baseAddr acct d1) hW fetch
      (CodeReq.SatisfiedBy_of_union_left hcr1) s hP hpc hex (by omega) hrr1
  have hfI : fetch 46 = some (.call .sol_invoke_signed_c) := hcr1 46 _ rfl
  have hInv0 : writerInv baseAddr (executeFn fetch s k0) := by
    have hAcct := bytes_of_holds (hl (hr hP))
    have hAcctI := bytes_of_holds (hl (hr hQ0))
    refine writerInv_of_mid hbase hbase' hacct hacctLen hfp hd1 hQ0 (by simp [hdepth]) ?_
    rw [executeFn_preserves_origPrivs,
      readMemBytes_congr _ s.mem _ _ (fun i hi => by
        rw [hAcctI i (by omega), hAcct i (by omega)])]
    exact hpriv
  have hInv : ∀ k, (executeFn fetch s k).pc = 46 → (executeFn fetch s k).exitCode = none →
      writerInv baseAddr (executeFn fetch s k) ∧
        (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + 46 := by
    intro k hk hke
    rw [Cpi.executeFn_invoke_unique fetch s 46 _ (Or.inr rfl) hfI hk hke hpc0 hex0]
    exact ⟨hInv0, by omega⟩
  -- The caller's path across the CPI, run by the runner.
  have hPath := Examples.Lifted.Sbpfv3CpiWriterLiftedSuccess.Sbpfv3CpiWriterLiftedSuccess_cpi_path
    baseAddr vR6Old vR2Old oldMemD_0 oldMemD_1 oldMemD_2 vR3Old oldMemD_3 oldMemD_4 oldMemD_5
    oldMemD_6 oldMemD_7 oldMemD_8 oldMemD_9 oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13
    oldMemD_14 vR7Old vR4Old vR5Old holdMemD_12_lt cpiRdOld cpiR0Old cpiFpOld0 cpi_oldMemB_1
    _ (writer_callee_contract baseAddr)
  obtain ⟨k1, hk1, hpc1, hex1, r, hrC, hstep, hcont⟩ :=
    Cpi.runner_cpiPath writerRegistry (Or.inr rfl) hPath (writerFrame baseAddr acct d1) hW
      fetch hcr1 hcr2 s hP hpc hex (by omega) hrr1 hrr2 (fun k a b => (hInv k a b).1) F
      (by omega)
  obtain ⟨hInvI, hcuI⟩ := hInv k1 hpc1 hex1
  -- The callee succeeds.
  obtain ⟨r0, hr0, hc0, hcu0'⟩ := writer_step_ok hInvI (F - k1 - 1) (by omega)
  rw [hr0] at hstep
  have hc : r.code = 0 := by
    have := congrArg (fun t => t.regs.r0) hstep
    simp only [chargeCu, Cpi.applyResult_r0] at this
    omega
  have hG : r.code = toU64 0 := by rw [hc]; rfl
  have hbud2 : (Cpi.applyResult (executeFn fetch s k1) r).cuConsumed + 6 + 0 ≤
      (Cpi.applyResult (executeFn fetch s k1) r).cuBudget := by
    rw [← hstep]
    simp only [chargeCu, Cpi.applyResult, executeFn_preserves_cuBudget]
    omega
  obtain ⟨k2, hk2, hpc2, hex2, hcu2, hPost, hrun⟩ := hcont hG hbud2
  -- The suffix end state.
  generalize hsE : executeFn fetch (Cpi.applyResult (executeFn fetch s k1) r) k2 = sE
    at hpc2 hex2 hcu2 hPost hrun
  have hPo := hl hPost
  have h42 : Cpi.committedByte r (effectiveAddr baseAddr 96) cpiFpOld0 = 42 := by
    unfold Cpi.committedByte
    rw [if_pos hc]
    exact writer_callee_value baseAddr _ r hrC hc
  have hr0E : sE.regs.r0 = 0 := by simpa using reg_of_holds (hl hPo)
  have hdE : sE.mem (baseAddr + 96) = 42 := by
    rw [← effectiveAddr_96, mem_of_holdsFor_memByteIs (hl (hr (hr hPo))), h42]
  have hmE : sE.mem (HEAP_START + 200) = 43 := by
    rw [show HEAP_START + 200 = effectiveAddr (toU64 12884902088) 0 from rfl,
      mem_of_holdsFor_memByteIs (hl (hr (hr (hr (hr (hr hPo)))))), h42]
    rfl
  have hcsE : sE.callStack = [] := by
    unfold writerFrame at hPost
    exact callStack_of_holds (hr (hr (hr (hr hPost))))
  have hbudE : sE.cuConsumed ≤ sE.cuBudget := by
    have : sE.cuBudget = (Cpi.applyResult (executeFn fetch s k1) r).cuBudget := by
      rw [← hsE, executeFn_preserves_cuBudget]
    omega
  obtain ⟨k, hk⟩ : ∃ k, F - k1 - 1 - k2 = k + 1 := ⟨F - k1 - 1 - k2 - 1, by omega⟩
  rw [hk] at hrun
  obtain ⟨hxF, hmF⟩ := runner_exit writerRegistry fetch sE k hex2 hbudE (hpc2 ▸ hexit) hcsE
  refine ⟨sE, k, hpc2, hex2, hr0E, hdE, hmE, hrun, ?_, ?_⟩
  · rw [hrun, hxF, hr0E]
  · rw [hrun, hmF]

/-! ## Sanity run -/

/-- A test program id: `n` little-endian in the low two bytes. -/
def pidBytes (n : Nat) : ByteArray :=
  ⟨#[(n % 256).toUInt8, (n / 256).toUInt8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- The writable data account of the writer differential test: key
    `pid(442)`, owned by the callee, 1_000_000 lamports, data `[0, 0]`. -/
def dataAcct : ParsedAcct :=
  { key := pidBytes 442, owner := writerCalleeId, lamports := 1000000, dataLen := 2,
    data := ⟨#[0, 0]⟩, isSigner := false, isWritable := true, executable := false,
    rentEpoch := 0, ownerPtr := 0, lamportsRefAddr := 0, dataPtr := 0, dataLenRefAddr := 0 }

/-- The callee's program account (read-only, executable). -/
def calleeAcct : ParsedAcct :=
  { key := writerCalleeId, owner := pidBytes 2, lamports := 1, dataLen := 0,
    data := ByteArray.empty, isSigner := false, isWritable := false, executable := true,
    rentEpoch := 0, ownerPtr := 0, lamportsRefAddr := 0, dataPtr := 0, dataLenRefAddr := 0 }

/-- The caller's serialized input: the data account, then the callee's
    program account, no instruction data, caller id `pid(440)`. -/
def writerInput : ByteArray :=
  buildCpiSubInputN (buildAcctSlots [dataAcct, calleeAcct]) (pidBytes 440) ByteArray.empty

/-- The runner, on the pinned caller ELF with `writerRegistry`, exits with
    code 0, account data `[42, 0]` and the heap marker 43: the concrete run
    `writer_end_to_end` describes. -/
theorem writer_runs :
    (runElf Examples.Lifted.Sbpfv3CpiWriterLifted.Sbpfv3CpiWriterLiftedElf
        { input := writerInput, programRegistry := writerRegistry }).map
      (fun s => (s.exitCode, s.mem (INPUT_START + 96), s.mem (INPUT_START + 97),
        s.mem (HEAP_START + 200))) = some (some 0, 42, 0, 43) := by
  native_decide

end Examples.CpiWriterEndToEnd
