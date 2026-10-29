/-
Run a batch of fd_vm-harness cases (format: caselib.py) through qedsvm and
print one outcome line per case, for `diffcase.py`.

  lake build qedcase && .lake/build/bin/qedcase <batch.bin>

Setup mirrors the harness: V0 maps the program image (`rodata`) read-only at
0x1_0000_0000; V3 maps rodata at 0 and text at 0x1_0000_0000 (with its slot
map). Text is decoded with the case's version; V0 registry = calldests (+ the
entrypoint symbol at `entry_pc`). Stack (64 x 4 KiB), heap (`heap_max`) and one
flat writable input region; register overrides after init; no CPI registry.
qedsvm has no fd_vm feature flags: it always models the gap-free stack.
-/
import SVM.SBPF.Runner
import SVM.SBPF.Outcome

open SVM.SBPF SVM.SBPF.Memory

def u64At (b : ByteArray) (off : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (b.get! (off + i)).toNat * 256 ^ i) 0

def slice (b : ByteArray) (off len : Nat) : ByteArray := b.extract off (off + len)

def pad8 (n : Nat) : Nat := (n + 7) / 8 * 8

def hex (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "0x" ++ String.ofList (List.replicate (16 - s.length) '0') ++ s

def fnv (b : ByteArray) : Nat :=
  b.foldl (fun h x => ((h ^^^ x.toNat) * 0x100000001b3) % 2 ^ 64) 0xcbf29ce484222325

def setReg (rf : RegFile) : Nat → Nat → RegFile
  | 0, v => { rf with r0 := v } | 1, v => { rf with r1 := v } | 2, v => { rf with r2 := v }
  | 3, v => { rf with r3 := v } | 4, v => { rf with r4 := v } | 5, v => { rf with r5 := v }
  | 6, v => { rf with r6 := v } | 7, v => { rf with r7 := v } | 8, v => { rf with r8 := v }
  | 9, v => { rf with r9 := v } | 10, v => { rf with r10 := v } | _, _ => rf

/-- Run the case whose header starts at byte `h`; returns its outcome line. -/
def runCase (b : ByteArray) (idx h : Nat) : String := Id.run do
  let w (i : Nat) := u64At b (h + 8 * i)
  let ver := w 0; let entryPc := w 1; let budget := w 2; let heapMax := w 3
  let textCnt := w 4; let rodataSz := w 5; let inputSz := w 6; let cdCnt := w 7
  let r2 := w 8; let textOff := w 9; let regMask := w 11
  let textAt   := h + 8 * 24
  let text     := slice b textAt (8 * textCnt)
  let rodataAt := textAt + 8 * textCnt
  let rodata   := slice b rodataAt rodataSz
  let inputAt  := rodataAt + pad8 rodataSz
  let input    := slice b inputAt inputSz
  let cdAt     := inputAt + pad8 inputSz
  let cdests   := (List.range cdCnt).map fun i => u64At b (cdAt + 8 * i)
  let version : Decode.Version := if ver ≥ 3 then .v3 else .v0
  let fnReg := (Elf.entrypointHash, entryPc) :: cdests.map fun pc => (Elf.pcHash pc, pc)
  let pre := s!"QED case={idx}"
  let some insns := Decode.decodeProgram text (if version == .v3 then [] else fnReg) version
    | return s!"{pre} decode=fail"
  let slotMap := Decode.buildSlotMap text
  let progBase := if version == .v3 then 0 else MM_REGION_SIZE
  let mem₀ := Runner.loadBytesAt (Runner.loadInput Runner.emptyMem input) rodata progBase
  let mem := if version == .v3 then Runner.loadBytesAt mem₀ text MM_REGION_SIZE else mem₀
  -- callx resolves through the text's slot map: V3 text at MM_REGION_SIZE, V0
  -- text inside the program image (`rodata`) at `text_off`.
  let textAddr := MM_REGION_SIZE + (if version == .v3 then 0 else textOff)
  let regions :=
    { start := textAddr, size := text.size, writable := false, textSlots := slotMap } ::
    [ { start := progBase,    size := rodataSz,          writable := false }
    , { start := STACK_START, size := Runner.STACK_SIZE, writable := true }
    , { start := HEAP_START,  size := heapMax,           writable := true }
    , { start := INPUT_START, size := inputSz,           writable := true } ]
  let regs₀ : RegFile := { r1 := INPUT_START, r2 := r2, r10 := STACK_START + 0x1000 }
  let regs := (List.range 11).foldl (fun rf i =>
    if regMask / 2 ^ i % 2 = 1 then setReg rf i (w (12 + i)) else rf) regs₀
  let s₀ : State :=
    { regs, mem, regions, pc := slotMap.getD entryPc 0, cuBudget := budget }
  let s := Runner.executeFnCpi (fun _ => none) (Runner.fetchFromArray insns) s₀ budget
  let outcome := match Outcome.ofState s inputSz budget with
    | .cuExceeded => "cu_exhausted"
    | .fault e _ => s!"fault:{repr e}"
    | .ok c .. => s!"exit:{hex c}"
  let rf := s.regs
  let regStr := String.intercalate " " <| (List.range 11).map fun i =>
    s!"r{i}={hex (rf.get ([Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10].getD i .r0))}"
  return s!"{pre} outcome={outcome} {regStr} pc_logical={s.pc} cu_used={hex (s.cuUsed budget)} cu_consumed_raw={s.cuConsumed} frames={s.callStack.length} input_fnv={hex (fnv (Runner.readMemBytes s.mem INPUT_START inputSz))}"

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: QedCase <batch.bin>"; return 2
  let b ← IO.FS.readBinFile path
  unless u64At b 0 = 0x0032544142564446 do IO.eprintln "bad magic"; return 2
  let cnt := u64At b 8
  let mut off := 16
  for i in [0:cnt] do
    let lenWords := u64At b off
    IO.println (runCase b i (off + 8))
    off := off + 8 + 8 * lenWords
  return 0
