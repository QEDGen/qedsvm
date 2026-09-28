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

end Examples.CpiWriterEndToEnd
