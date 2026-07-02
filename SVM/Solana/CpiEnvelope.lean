/-
  CPI envelope encoding (#40 gap 4) — the memory-side view of the
  `CpiInstruction` a program hands `sol_invoke_signed`, as an SL assertion
  over the caller's cells.

  Rust ABI (`StableInstruction`), exactly as the diff-validated runner
  decodes it (`Runner.cpiCallNextState`):

      r1+0   accounts StableVec ptr      (the AccountMeta array)
      r1+8   accounts StableVec cap
      r1+16  accounts StableVec len      ← runner `accountCount`
      r1+24  data StableVec ptr          ← runner `ixDataPtr`
      r1+32  data StableVec cap
      r1+40  data StableVec len          ← runner `ixDataLen`
      r1+48  program id, 32 bytes inline ← runner `pid`

  `AccountMeta` cells are 34 bytes: pubkey (32) + is_signer (1) +
  is_writable (1).

  A lift that owns these cells at an invoke call site therefore pins the
  ENVELOPE EVENT — program id, account metas, data bytes — the binary hands
  the syscall: qedgen's per-call-site CPI theorems become claims about
  `cpiEnvelope … ix` in a lifted pre instead of axioms. `cpiEnvelope_reads`
  is the bridge to the runner's exact reads (via the #48 forward bridges).

  NOT claimed here: what the invoke DOES (the proof-facing CPI is the
  fail-closed `Cpi.exec` stub — audit C5), or the byte-fold form of the
  runner's 32-byte pid read (bridged at `pubkeyAt` granularity).
-/

import SVM.Solana.Cpi
import SVM.SBPF.CodecRead

namespace SVM.Solana

open SVM.SBPF SVM.SBPF.Memory

/-- Instruction data bytes as a `ByteArray` (for the `↦Bytes` blob). -/
def dataBA (data : List Nat) : ByteArray :=
  ⟨(data.map (fun b => UInt8.ofNat b)).toArray⟩

/-- Serialized `AccountMeta` array at `addr`: 34-byte cells of
    pubkey ‖ is_signer ‖ is_writable. -/
def metasSL (addr : Nat) : List Cpi.AccountMeta → Assertion
  | [] => emp
  | m :: rest =>
      pubkeyIs addr m.pubkey **
      memByteIs (addr + 32) (if m.isSigner then 1 else 0) **
      memByteIs (addr + 33) (if m.isWritable then 1 else 0) **
      metasSL (addr + 34) rest

@[simp] theorem metasSL_nil (addr : Nat) : metasSL addr [] = emp := rfl

@[simp] theorem metasSL_cons (addr : Nat) (m : Cpi.AccountMeta)
    (rest : List Cpi.AccountMeta) :
    metasSL addr (m :: rest) =
      (pubkeyIs addr m.pubkey **
       memByteIs (addr + 32) (if m.isSigner then 1 else 0) **
       memByteIs (addr + 33) (if m.isWritable then 1 else 0) **
       metasSL (addr + 34) rest) := rfl

/-- The Rust-ABI `StableInstruction` envelope at `instrAddr` (the syscall's
    `r1`), encoding `ix`: the two StableVec headers, the inline program id,
    the data bytes at `dataPtr`, the metas array at `metasPtr` (last, so the
    zero-meta case reduces via `sepConj_emp_right_eq`). `metasCap` /
    `dataCap` are allocator artifacts the runner never reads — parameters,
    not claims. -/
def cpiEnvelope (instrAddr metasPtr metasCap dataPtr dataCap : Nat)
    (ix : Cpi.CpiInstruction) : Assertion :=
  (instrAddr ↦U64 metasPtr) **
  ((instrAddr + 8) ↦U64 metasCap) **
  ((instrAddr + 16) ↦U64 ix.accounts.length) **
  ((instrAddr + 24) ↦U64 dataPtr) **
  ((instrAddr + 32) ↦U64 dataCap) **
  ((instrAddr + 40) ↦U64 ix.data.length) **
  pubkeyIs (instrAddr + 48) ix.programId **
  memBytesIs dataPtr (dataBA ix.data) **
  metasSL metasPtr ix.accounts

/-- **Envelope → runner reads.** A state satisfying the envelope answers the
    EXACT reads `Runner.cpiCallNextState` performs on the caller: the meta
    count at +16, the data pointer at +24, the data length at +40, and the
    inline program id at +48 (at `pubkeyAt` limb granularity). So an invoke
    executed from an envelope-owning state dispatches `ix` — the trace-level
    event is pinned by the caller's memory, not an axiom. -/
theorem cpiEnvelope_reads
    (instrAddr metasPtr metasCap dataPtr dataCap : Nat)
    (ix : Cpi.CpiInstruction) {s : State}
    (hb0 : ix.programId.c0 < 2 ^ 64) (hb1 : ix.programId.c1 < 2 ^ 64)
    (hb2 : ix.programId.c2 < 2 ^ 64) (hb3 : ix.programId.c3 < 2 ^ 64)
    (h : (cpiEnvelope instrAddr metasPtr metasCap dataPtr dataCap ix).holdsFor s) :
    readU64 s.mem (instrAddr + 16) = ix.accounts.length % 2 ^ 64 ∧
    readU64 s.mem (instrAddr + 24) = dataPtr % 2 ^ 64 ∧
    readU64 s.mem (instrAddr + 40) = ix.data.length % 2 ^ 64 ∧
    pubkeyAt s.mem (instrAddr + 48) ix.programId := by
  unfold cpiEnvelope at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact readU64_of_holdsFor_memU64Is
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right h)))
  · exact readU64_of_holdsFor_memU64Is
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right
        (holdsFor_sepConj_right h))))
  · exact readU64_of_holdsFor_memU64Is
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right
        (holdsFor_sepConj_right (holdsFor_sepConj_right
          (holdsFor_sepConj_right h))))))
  · exact pubkeyAt_of_holdsFor_pubkeyIs hb0 hb1 hb2 hb3
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right
        (holdsFor_sepConj_right (holdsFor_sepConj_right
          (holdsFor_sepConj_right (holdsFor_sepConj_right h)))))))

/-! ## C-ABI variant (`sol_invoke_signed_c`)

`SolInstruction`: program-id POINTER at +0 (the 32 bytes live behind it),
accounts ptr/len at +8/+16, data ptr/len at +24/+32 — exactly the fields
`Runner.cpiCallNextState` decodes on the C path. Meta CONTENT there comes
from the account-infos array, not the instruction, so it is not encoded
here (the count is). -/

def cpiEnvelopeC (instrAddr pidPtr metasPtr dataPtr : Nat)
    (ix : Cpi.CpiInstruction) : Assertion :=
  (instrAddr ↦U64 pidPtr) **
  ((instrAddr + 8) ↦U64 metasPtr) **
  ((instrAddr + 16) ↦U64 ix.accounts.length) **
  ((instrAddr + 24) ↦U64 dataPtr) **
  ((instrAddr + 32) ↦U64 ix.data.length) **
  pubkeyIs pidPtr ix.programId **
  memBytesIs dataPtr (dataBA ix.data)

/-- **C-ABI envelope → runner reads** (mirror of `cpiEnvelope_reads`): the
    program-id pointer at +0, meta count at +16, data pointer at +24, data
    length at +32, and the pointed-to program id at `pubkeyAt` granularity. -/
theorem cpiEnvelopeC_reads
    (instrAddr pidPtr metasPtr dataPtr : Nat)
    (ix : Cpi.CpiInstruction) {s : State}
    (hb0 : ix.programId.c0 < 2 ^ 64) (hb1 : ix.programId.c1 < 2 ^ 64)
    (hb2 : ix.programId.c2 < 2 ^ 64) (hb3 : ix.programId.c3 < 2 ^ 64)
    (h : (cpiEnvelopeC instrAddr pidPtr metasPtr dataPtr ix).holdsFor s) :
    readU64 s.mem instrAddr = pidPtr % 2 ^ 64 ∧
    readU64 s.mem (instrAddr + 16) = ix.accounts.length % 2 ^ 64 ∧
    readU64 s.mem (instrAddr + 24) = dataPtr % 2 ^ 64 ∧
    readU64 s.mem (instrAddr + 32) = ix.data.length % 2 ^ 64 ∧
    pubkeyAt s.mem pidPtr ix.programId := by
  unfold cpiEnvelopeC at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact readU64_of_holdsFor_memU64Is (holdsFor_sepConj_left h)
  · exact readU64_of_holdsFor_memU64Is
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right h)))
  · exact readU64_of_holdsFor_memU64Is
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right
        (holdsFor_sepConj_right h))))
  · exact readU64_of_holdsFor_memU64Is
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right
        (holdsFor_sepConj_right (holdsFor_sepConj_right h)))))
  · exact pubkeyAt_of_holdsFor_pubkeyIs hb0 hb1 hb2 hb3
      (holdsFor_sepConj_left (holdsFor_sepConj_right (holdsFor_sepConj_right
        (holdsFor_sepConj_right (holdsFor_sepConj_right
          (holdsFor_sepConj_right h))))))

/-! ## The runner's literal pid read (#40 gap 4, last bridge)

`Runner.cpiCallNextState` reads the program id as four little-endian u64
limbs combined with `2^64`-powers (the byte-wise fold was refactored to this
kernel-friendly shape). `cpiEnvelope_pid_read` composes `cpiEnvelope_reads`
with that exact expression: an envelope-owning state makes the runner's
`pid` variable LITERALLY the encoded `ix.programId` — closing the last gap
between the SL envelope and the runner's decode. -/

/-- **Envelope → the runner's pid.** The runner's program-id read (four
    `readU64` limbs at the inline id cells, combined little-endian) recovers
    exactly the encoded `ix.programId`. -/
theorem cpiEnvelope_pid_read
    (instrAddr metasPtr metasCap dataPtr dataCap : Nat)
    (ix : Cpi.CpiInstruction) {s : State}
    (hb0 : ix.programId.c0 < 2 ^ 64) (hb1 : ix.programId.c1 < 2 ^ 64)
    (hb2 : ix.programId.c2 < 2 ^ 64) (hb3 : ix.programId.c3 < 2 ^ 64)
    (h : (cpiEnvelope instrAddr metasPtr metasCap dataPtr dataCap ix).holdsFor s) :
    readU64 s.mem (instrAddr + 48)
      + readU64 s.mem (instrAddr + 48 + 8) * 2 ^ 64
      + readU64 s.mem (instrAddr + 48 + 16) * 2 ^ 128
      + readU64 s.mem (instrAddr + 48 + 24) * 2 ^ 192
      = ix.programId.c0 + ix.programId.c1 * 2 ^ 64
        + ix.programId.c2 * 2 ^ 128 + ix.programId.c3 * 2 ^ 192 := by
  obtain ⟨p0, p1, p2, p3⟩ :=
    (cpiEnvelope_reads instrAddr metasPtr metasCap dataPtr dataCap ix
      hb0 hb1 hb2 hb3 h).2.2.2
  rw [p0, p1, p2, p3]

/-- The C-ABI analog: the pid read at the POINTED-TO address. -/
theorem cpiEnvelopeC_pid_read
    (instrAddr pidPtr metasPtr dataPtr : Nat)
    (ix : Cpi.CpiInstruction) {s : State}
    (hb0 : ix.programId.c0 < 2 ^ 64) (hb1 : ix.programId.c1 < 2 ^ 64)
    (hb2 : ix.programId.c2 < 2 ^ 64) (hb3 : ix.programId.c3 < 2 ^ 64)
    (h : (cpiEnvelopeC instrAddr pidPtr metasPtr dataPtr ix).holdsFor s) :
    readU64 s.mem pidPtr
      + readU64 s.mem (pidPtr + 8) * 2 ^ 64
      + readU64 s.mem (pidPtr + 16) * 2 ^ 128
      + readU64 s.mem (pidPtr + 24) * 2 ^ 192
      = ix.programId.c0 + ix.programId.c1 * 2 ^ 64
        + ix.programId.c2 * 2 ^ 128 + ix.programId.c3 * 2 ^ 192 := by
  obtain ⟨p0, p1, p2, p3⟩ :=
    (cpiEnvelopeC_reads instrAddr pidPtr metasPtr dataPtr ix
      hb0 hb1 hb2 hb3 h).2.2.2.2
  rw [p0, p1, p2, p3]

end SVM.Solana
