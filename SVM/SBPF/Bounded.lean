/-
  Boundedness invariant of reachable machine states (audit L5 + L3).

  `State` stores registers and memory bytes as unbounded `Nat`. Every
  `step` arm truncates what it writes (`wrapAdd`/`% U64_MODULUS`/
  `signExtend32`/width-bounded loads; `Mem.put` reduces mod 256), so the
  u64-register / u8-byte invariants hold for every REACHABLE state — but
  until now that was discipline, not a theorem. This file states the
  invariant (`StateBounded`) and proves the base cases; preservation
  through `step`/`executeFn` lives alongside.

  Why it matters (not cosmetics):
  - The unsigned compares (`jgt`/`jge`/`jlt`/`jle`) compare RAW `Nat`
    register values; they are faithful u64 compares only on register
    values `< 2^64` (L5).
  - A byte atom `a ↦ₘ v` stores `v` raw; it is faithful to an 8-bit cell
    only for `v < 256`. `mem_lt` makes a `v ≥ 256` atom UNSATISFIABLE
    against any reachable state's memory, fencing the L3 footgun without
    touching `singletonMem` or any byte-cell spec (canonicalising the
    atom definition was attempted and reverted — it ripples `< 256`
    hypotheses through the generic byte-cell specs into the H8
    byte-demotion base).

  The r10 component is NOT a flat bound: `call_local` bumps r10 by
  0x1000, which `r10 < 2^64` alone cannot re-establish. The invariant
  carries the exact V0 frame discipline (`StackR10WF`): r10 sits exactly
  one frame above the top saved frame pointer, grounding out at
  `STACK_START + 0x1000`, so `r10 = STACK_START + 0x1000·(depth+1)` and
  the `MAX_CALL_DEPTH` guard bounds it absolutely.
-/

import SVM.SBPF.Runner

namespace SVM.SBPF
open Memory

/-! ## The r10 / call-stack discipline -/

/-- The V0 frame discipline relating the call stack to the live frame
    pointer: `r10` is exactly one 0x1000 frame above the top frame's
    saved r10, recursively down to the initial `STACK_START + 0x1000`.
    `call_local` (push + bump) and `exit` (pop + restore) both preserve
    it; `RegFile.set` cannot write r10 at all (`RegFile.set_r10`). -/
def StackR10WF : List CallFrame → Nat → Prop
  | [], r10 => r10 = STACK_START + 0x1000
  | f :: rest, r10 => r10 = f.savedR10 + 0x1000 ∧ StackR10WF rest f.savedR10

/-- The frame discipline pins r10 exactly: one frame per stack entry
    above the base. -/
theorem StackR10WF.r10_eq :
    ∀ {st : List CallFrame} {r10 : Nat}, StackR10WF st r10 →
      r10 = STACK_START + 0x1000 * (st.length + 1)
  | [], _, h => by simpa [StackR10WF] using h
  | f :: rest, r10, h => by
    obtain ⟨htop, hrest⟩ := h
    have := StackR10WF.r10_eq hrest
    subst htop
    simp only [this, List.length_cons]
    omega

/-! ## The invariant -/

/-- Boundedness of a machine state — what every state reachable from
    `initState`/`Runner.initialState` satisfies (audit L5 + L3).

    `regs_lt` covers r10 too (derivable from `stack_r10` + `stack_depth`,
    but carried directly so consumers don't re-derive it).

    `heapNext_le`: `allocFreeStep` only advances the bump pointer when
    the result stays within the 32 KiB heap (`0x300000000 + 0x8000`).

    `returnData_le`: `ReturnData.execSet` rejects `len > 1024`
    (`ERR_RETURN_DATA_TOO_LARGE`), so the buffer never exceeds the agave
    cap — which bounds the `r0 := returnData.size` write in `execGet`.

    `mem_lt`: every byte readable from `Mem` is a real byte. Writes go
    through `Mem.put` (`% 256`); syscall bulk writes construct a new
    default function whose branches read `ByteArray`s (`UInt8.toNat`,
    `< 256`) or fall through to the previous memory. -/
structure StateBounded (s : State) : Prop where
  regs_lt : ∀ r, s.regs.get r < U64_MODULUS
  stack_r10 : StackR10WF s.callStack s.regs.r10
  stack_depth : s.callStack.length ≤ MAX_CALL_DEPTH
  frames_lt : ∀ f ∈ s.callStack,
    f.savedR6 < U64_MODULUS ∧ f.savedR7 < U64_MODULUS ∧
    f.savedR8 < U64_MODULUS ∧ f.savedR9 < U64_MODULUS
  cuBudget_lt : s.cuBudget < U64_MODULUS
  heapNext_le : s.heapNext ≤ 0x300008000
  returnData_le : s.returnData.size ≤ 1024
  mem_lt : ∀ a, s.mem a < 256

/-- The frame pointer of a bounded state is pinned by its call depth. -/
theorem StateBounded.r10_eq {s : State} (h : StateBounded s) :
    s.regs.r10 = STACK_START + 0x1000 * (s.callStack.length + 1) :=
  h.stack_r10.r10_eq

/-- Absolute frame-pointer bound: at most `MAX_CALL_DEPTH` frames deep,
    r10 stays below `STACK_START + 0x1000·65` (`< 2^64` with room). -/
theorem StateBounded.r10_le {s : State} (h : StateBounded s) :
    s.regs.r10 ≤ STACK_START + 0x1000 * (MAX_CALL_DEPTH + 1) := by
  rw [h.r10_eq]
  have := h.stack_depth
  simp only [STACK_START, MAX_CALL_DEPTH] at *
  omega

/-! ## Memory boundedness plumbing -/

/-- `Mem.put` writes a reduced byte and preserves all other reads. -/
theorem Mem.read_put_lt (m : Mem) (addr val : Nat)
    (h : ∀ x, m x < 256) : ∀ a, (Mem.put m addr val) a < 256 := by
  intro a
  by_cases hx : a = addr
  · subst hx
    rw [Memory.Mem.read_put_self]
    exact Nat.mod_lt _ (by decide)
  · rw [Memory.Mem.read_put_other _ _ _ _ hx]
    exact h a

/-- The empty memory reads 0 everywhere. -/
theorem emptyMem_lt : ∀ a, (Runner.emptyMem : Mem) a < 256 := by
  intro a
  show Mem.read {} a < 256
  unfold Mem.read
  simp

/-- `loadBytesAt` (the input/section loader) preserves byte-boundedness:
    each write goes through `Memory.writeU8` = `Mem.put`. -/
theorem loadBytesAt_lt (bytes : ByteArray) (base : Nat) :
    ∀ (mem : Mem), (∀ a, mem a < 256) →
      ∀ a, (Runner.loadBytesAt mem bytes base) a < 256 := by
  unfold Runner.loadBytesAt
  generalize List.range bytes.size = idxs
  induction idxs with
  | nil => intro mem h a; simpa using h a
  | cons i rest ih =>
    intro mem h a
    simp only [List.foldl_cons]
    exact ih _ (fun x => by
      unfold Memory.writeU8
      exact Mem.read_put_lt _ _ _ h x) a

/-- `loadInput` establishes byte-boundedness over the empty memory. -/
theorem loadInput_lt (input : ByteArray) :
    ∀ a, (Runner.loadInput Runner.emptyMem input) a < 256 := by
  unfold Runner.loadInput
  exact loadBytesAt_lt _ _ _ emptyMem_lt

/-! ## Arithmetic bound lemmas

Every value a `step` arm writes into a register is `< 2^64` by one of
these. -/

theorem wrapAdd_lt (a b : Nat) : wrapAdd a b < U64_MODULUS :=
  Nat.mod_lt _ (by decide)
theorem wrapSub_lt (a b : Nat) : wrapSub a b < U64_MODULUS :=
  Nat.mod_lt _ (by decide)
theorem wrapMul_lt (a b : Nat) : wrapMul a b < U64_MODULUS :=
  Nat.mod_lt _ (by decide)
theorem wrapNeg_lt (a : Nat) : wrapNeg a < U64_MODULUS :=
  Nat.mod_lt _ (by decide)

theorem signExtend32_lt {n : Nat} (h : n < U32_MODULUS) :
    signExtend32 n < U64_MODULUS := by
  simp only [signExtend32, U32_MODULUS, U64_MODULUS] at *
  split <;> omega

theorem wrapAdd32_lt (a b : Nat) : wrapAdd32 a b < U64_MODULUS :=
  signExtend32_lt (Nat.mod_lt _ (by decide))
theorem wrapSub32_lt (a b : Nat) : wrapSub32 a b < U64_MODULUS :=
  signExtend32_lt (Nat.mod_lt _ (by decide))
theorem wrapMul32_lt (a b : Nat) : wrapMul32 a b < U64_MODULUS :=
  signExtend32_lt (Nat.mod_lt _ (by decide))
theorem wrapNeg32_lt (a : Nat) : wrapNeg32 a < U64_MODULUS := by
  simp only [wrapNeg32, U32_MODULUS, U64_MODULUS]
  omega

/-- Sign-extended immediates land in u64 range. -/
theorem toU64_lt (v : Int) : toU64 v < U64_MODULUS := by
  simp only [toU64, U64_MODULUS]
  omega

theorem resolveSrc_lt {rf : RegFile} (h : ∀ r, rf.get r < U64_MODULUS)
    (src : Src) : resolveSrc rf src < U64_MODULUS := by
  cases src with
  | reg r => exact h r
  | imm v => exact toU64_lt v

/-- Memory loads are width-bounded UNCONDITIONALLY: `readU8/16/32/64`
    reduce each byte `% 256` themselves. -/
theorem readByWidth_lt (m : Mem) (addr : Nat) (w : Width) :
    Memory.readByWidth m addr w < U64_MODULUS := by
  cases w <;>
    simp only [Memory.readByWidth, Memory.readU8, Memory.readU16,
               Memory.readU32, Memory.readU64, U64_MODULUS] <;>
    omega

/-! ## Register-file bound plumbing -/

/-- Writing a bounded value preserves all-registers-bounded. Pure defeq
    case bash (`get`/`set` are `@[simp]` defs). -/
theorem RegFile.set_get_lt {rf : RegFile} {B : Nat}
    (h : ∀ r, rf.get r < B) {v : Nat} (hv : v < B) (dst : Reg) :
    ∀ r, (rf.set dst v).get r < B := by
  intro r
  cases dst <;> cases r <;>
    first
      | exact hv
      | exact h .r0 | exact h .r1 | exact h .r2 | exact h .r3
      | exact h .r4 | exact h .r5 | exact h .r6 | exact h .r7
      | exact h .r8 | exact h .r9 | exact h .r10

/-! ## Memory-write boundedness plumbing -/

/-- Any `foldl` of `writeU8`s preserves byte-boundedness (the common
    core of `loadBytesAt` and `writeBytes`). -/
theorem foldl_writeU8_lt (addrF valF : Nat → Nat) (idxs : List Nat) :
    ∀ (m : Mem), (∀ a, m a < 256) →
      ∀ a, (idxs.foldl (fun acc i =>
              Memory.writeU8 acc (addrF i) (valF i)) m) a < 256 := by
  induction idxs with
  | nil => intro m h a; simpa using h a
  | cons i rest ih =>
    intro m h a
    simp only [List.foldl_cons]
    exact ih _ (fun x => by
      unfold Memory.writeU8
      exact Mem.read_put_lt _ _ _ h x) a

/-- `writeBytes` (syscall bulk output: hashes, PDA results, …)
    preserves byte-boundedness. -/
theorem writeBytes_lt (out len : Nat) (bs : ByteArray) (m : Mem)
    (h : ∀ a, m a < 256) : ∀ a, (writeBytes m out len bs) a < 256 := by
  unfold writeBytes
  exact foldl_writeU8_lt _ _ _ m h

/-- `hashWrite`'s `mem` is either `s.mem` (a guard faulted) or
    `writeBytes s.mem outPtr outLen digest` (success); both are byte-bounded
    when `s.mem` is. The `mem_lt` sweep closes every hash arm with this (the
    recursive `guardSlices` stays folded). -/
theorem hashWrite_mem_lt (s : State) (outPtr outLen inPtr inN : Nat)
    (digest : ByteArray) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (s.hashWrite outPtr outLen inPtr inN digest).mem a < 256 := by
  simp only [State.hashWrite]
  refine State.guardWrite_mem_lt_of_k s _ _ _ a (h a) ?_
  refine State.guardRead_mem_lt_of_k s _ _ _ a (h a) ?_
  refine State.guardSlices_mem_lt_of_k s _ _ _ a (h a) ?_
  exact writeBytes_lt _ _ _ _ h a

/-! Per-hash `regs_lt` / `mem_lt` closers. Each unfolds its `exec` to the
folded `hashWrite` and applies the generic bound in a SMALL context. The
sweeps then close the hash arm by a cheap head-match (`exec` and its digest
stay folded — no metavars): applying the 5-metavar generic `hashWrite_*`
directly inside the 8M-heartbeat `mem_lt` sweep cost ~160s (the sha256
pure-Lean digest worst); these wrappers move that cost out, once each. -/
theorem Sha256_exec_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (Sha256.exec s).regs := by
  simp only [Sha256.exec]; exact State.hashWrite_regs_of_k s _ _ _ _ _ h0 hk

theorem Sha256_exec_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Sha256.exec s).mem a < 256 := by
  simp only [Sha256.exec]; exact hashWrite_mem_lt s _ _ _ _ _ h a

theorem Sha512_exec_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (Sha512.exec s).regs := by
  simp only [Sha512.exec]; exact State.hashWrite_regs_of_k s _ _ _ _ _ h0 hk

theorem Sha512_exec_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Sha512.exec s).mem a < 256 := by
  simp only [Sha512.exec]; exact hashWrite_mem_lt s _ _ _ _ _ h a

theorem Keccak256_exec_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (Keccak256.exec s).regs := by
  simp only [Keccak256.exec]; exact State.hashWrite_regs_of_k s _ _ _ _ _ h0 hk

theorem Keccak256_exec_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Keccak256.exec s).mem a < 256 := by
  simp only [Keccak256.exec]; exact hashWrite_mem_lt s _ _ _ _ _ h a

theorem Blake3_exec_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (Blake3.exec s).regs := by
  simp only [Blake3.exec]; exact State.hashWrite_regs_of_k s _ _ _ _ _ h0 hk

theorem Blake3_exec_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Blake3.exec s).mem a < 256 := by
  simp only [Blake3.exec]; exact hashWrite_mem_lt s _ _ _ _ _ h a

/-- `guardedCommit`'s `mem` is `s.mem` (guard miss or commitOptional's `none`)
    or `writeBytes …` (commitOptional's `some`), both byte-bounded. The poseidon
    `mem_lt` closer (its `commitOptional` body, not `hashWrite`'s `writeBytes`). -/
theorem guardedCommit_mem_lt (s : State) (outPtr outLen inPtr inN : Nat)
    (result : Option ByteArray) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (s.guardedCommit outPtr outLen inPtr inN result).mem a < 256 := by
  simp only [State.guardedCommit]
  refine State.guardWrite_mem_lt_of_k s _ _ _ a (h a) ?_
  refine State.guardRead_mem_lt_of_k s _ _ _ a (h a) ?_
  refine State.guardSlices_mem_lt_of_k s _ _ _ a (h a) ?_
  cases result
  · exact h a
  · exact writeBytes_lt _ _ _ _ h a

theorem Poseidon_exec_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk0 : motive (s.regs.set .r0 0))
    (hk1 : motive (s.regs.set .r0 1)) :
    motive (Poseidon.exec s).regs := by
  simp only [Poseidon.exec]
  exact State.guardedCommit_regs_of_k s _ _ _ _ _ h0 hk0 hk1

theorem Poseidon_exec_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Poseidon.exec s).mem a < 256 := by
  simp only [Poseidon.exec]; exact guardedCommit_mem_lt s _ _ _ _ _ h a

/-- A real byte. (`UInt8.toNat` is the shape every `ByteArray` read in
    a syscall bulk-write lambda produces.) -/
theorem byte_toNat_lt (u : UInt8) : u.toNat < 256 := by
  first
    | exact u.toNat_lt_size
    | exact u.toNat_lt
    | exact Nat.lt_of_lt_of_le u.toBitVec.isLt (by decide)

/-- `execCreate` = `guardRead` (program_id) wrapping `guardedCommit` (output +
    descriptors + slices + `commitOptional`); its `regs` is `s.regs` (a guard
    miss) or `set .r0 {0,1}` (commitOptional). The PDA `regs_lt` closer. -/
theorem Pda_execCreate_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk0 : motive (s.regs.set .r0 0))
    (hk1 : motive (s.regs.set .r0 1)) :
    motive (Pda.execCreate s).regs := by
  simp only [Pda.execCreate]
  refine State.guardRead_regs_of_k s _ _ _ h0 ?_
  exact State.guardedCommit_regs_of_k s _ _ _ _ _ h0 hk0 hk1

theorem Pda_execCreate_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Pda.execCreate s).mem a < 256 := by
  simp only [Pda.execCreate]
  refine State.guardRead_mem_lt_of_k s _ _ _ a (h a) ?_
  exact guardedCommit_mem_lt s _ _ _ _ _ h a

/-- `execTryFind` = three input guards (program_id / descriptors / slices)
    wrapping a `some` arm (two output guards → PDA + bump write) or a `none`
    arm (`set .r0 1`). Its `regs` is `s.regs` (a guard miss) or `set .r0 {0,1}`.
    The PDA-try-find `regs_lt` closer. -/
theorem Pda_execTryFind_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk0 : motive (s.regs.set .r0 0))
    (hk1 : motive (s.regs.set .r0 1)) :
    motive (Pda.execTryFind s).regs := by
  simp only [Pda.execTryFind]
  refine State.guardRead_regs_of_k s _ _ _ h0 ?_
  refine State.guardRead_regs_of_k s _ _ _ h0 ?_
  refine State.guardSlices_regs_of_k s _ _ _ h0 ?_
  split
  · refine State.guardWrite_regs_of_k s _ _ _ h0 ?_
    refine State.guardWrite_regs_of_k s _ _ _ h0 ?_
    exact hk0
  · exact hk1


/-- Width-dispatched stores preserve byte-boundedness: every width is a
    chain of `Mem.put`s. -/
theorem writeByWidth_lt (m : Mem) (addr val : Nat) (w : Width)
    (h : ∀ a, m a < 256) : ∀ a, (Memory.writeByWidth m addr val w) a < 256 := by
  cases w <;>
    simp only [Memory.writeByWidth, Memory.writeU8, Memory.writeU16,
               Memory.writeU32, Memory.writeU64] <;>
    repeat' first
      | exact h
      | apply Mem.read_put_lt

/-- Reading a function-coerced `Mem` (the syscall bulk-write idiom
    `let mem' : Memory.Mem := fun a => …`) is the function itself: the
    coercion installs it as `default` with an empty overlay. -/
theorem Mem.read_coe (f : Nat → Nat) (a : Nat) : ((f : Mem) : Nat → Nat) a = f a := by
  show Mem.read { default := f } a = f a
  unfold Mem.read
  simp


/-- Bound for reading ANY constructor-literal `Mem` (the shape a
    syscall's `let mem' : Memory.Mem := fun a => …` coercion produces),
    overlay-agnostic: an overlay hit is a real `UInt8`; a miss lands in
    the default function. `apply`-unifies regardless of how the empty
    overlay's `{}` elaborated (a rewrite keyed on a specific `{}` term
    does NOT reliably match — learned the hard way). -/
theorem Mem.read_mk_lt (f : Nat → Nat) (o : Std.HashMap Nat UInt8)
    (a : Nat) (hf : ∀ x, f x < 256) : Mem.read ⟨f, o⟩ a < 256 := by
  unfold Mem.read
  split
  · exact byte_toNat_lt _
  · exact hf a

/-- Peel one `ite` off a bound goal. Closing if-chains by `repeat`ed
    `apply ite_lt` instead of `split` matters: after `apply
    Mem.read_mk_lt; intro x` the chain goal is a BETA-REDEX
    (`(fun a => if …) x < 256`), which `split` cannot see through
    (syntactic ite search) and which the `simp`/`dsimp` beta route
    cannot normalize without max-stepping on `Mem.read`'s `HashMap`
    internals — but `apply` unifies up to defeq, so it reads straight
    through the redex. -/
theorem ite_lt {c : Prop} [Decidable c] {t e B : Nat}
    (ht : t < B) (he : e < B) : (if c then t else e) < B := by
  split
  · exact ht
  · exact he

/-- `mem_lt` closers for the de-simp'd rent / epoch_schedule sysvars: peel the
    `guardWrite` (fault keeps `s.mem`), then the lambda-coerced multi-`if` write
    is bounded by `Mem.read_mk_lt` + repeated `ite_lt` (byte literals / old mem). -/
theorem execRent_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Sysvar.execRent s).mem a < 256 := by
  simp only [Sysvar.execRent]
  refine State.guardWrite_mem_lt_of_k s _ _ _ a (h a) ?_
  apply Mem.read_mk_lt
  intro x
  repeat first
    | omega
    | exact h _
    | apply ite_lt

theorem execEpochSchedule_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Sysvar.execEpochSchedule s).mem a < 256 := by
  simp only [Sysvar.execEpochSchedule]
  refine State.guardWrite_mem_lt_of_k s _ _ _ a (h a) ?_
  apply Mem.read_mk_lt
  intro x
  repeat first
    | omega
    | exact h _
    | apply ite_lt

/-- `execTryFind` `mem_lt` closer (placed after `Mem.read_mk_lt` / `ite_lt`):
    peel the three input guards (mem-preserving) → `some` arm's two output
    guards → the coerced `mem'` lambda (bump byte / 32-byte PDA `writeBytes`);
    the `none` arm keeps `s.mem`. -/
theorem Pda_execTryFind_mem_lt (s : State) (h : ∀ a, s.mem a < 256) (a : Nat) :
    (Pda.execTryFind s).mem a < 256 := by
  simp only [Pda.execTryFind]
  refine State.guardRead_mem_lt_of_k s _ _ _ a (h a) ?_
  refine State.guardRead_mem_lt_of_k s _ _ _ a (h a) ?_
  refine State.guardSlices_mem_lt_of_k s _ _ _ a (h a) ?_
  split
  · refine State.guardWrite_mem_lt_of_k s _ _ _ a (h a) ?_
    refine State.guardWrite_mem_lt_of_k s _ _ _ a (h a) ?_
    apply Mem.read_mk_lt
    intro x
    apply ite_lt
    · exact byte_toNat_lt _
    · exact writeBytes_lt _ _ _ _ h _
  · exact h a

/-! ## State-shape preservation lemmas

`step`'s arms are record updates of a handful of shapes; one lemma per
shape keeps `step_bounded` a clean case bash. -/

/-- Arms `{ s with regs := s.regs.set dst v, pc := pc' }` — the bulk of
    the ALU/load ISA. The frame discipline survives because `RegFile.set`
    cannot write r10 (`RegFile.set_preserves_r10`). -/
theorem StateBounded.with_set_reg {s : State} (h : StateBounded s)
    {dst : Reg} {v : Nat} (hv : v < U64_MODULUS) (pc' : Nat) :
    StateBounded { s with regs := s.regs.set dst v, pc := pc' } :=
  { regs_lt := RegFile.set_get_lt h.regs_lt hv dst
    stack_r10 := by
      show StackR10WF s.callStack (s.regs.set dst v).r10
      rw [RegFile.set_preserves_r10]
      exact h.stack_r10
    stack_depth := h.stack_depth
    frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt
    heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le
    mem_lt := h.mem_lt }

/-- Arms `{ s with pc := … }` (all jumps). -/
theorem StateBounded.with_pc {s : State} (h : StateBounded s) (pc' : Nat) :
    StateBounded { s with pc := pc' } :=
  { regs_lt := h.regs_lt, stack_r10 := h.stack_r10
    stack_depth := h.stack_depth, frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt, heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le, mem_lt := h.mem_lt }

/-- Arms `{ s with exitCode := … }` (the clean program exit). -/
theorem StateBounded.with_exitCode {s : State} (h : StateBounded s)
    (e : Option Nat) : StateBounded { s with exitCode := e } :=
  { regs_lt := h.regs_lt, stack_r10 := h.stack_r10
    stack_depth := h.stack_depth, frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt, heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le, mem_lt := h.mem_lt }

/-- Arms `{ s with exitCode := …, vmError := … }` (every fail-closed
    abort — audit L1: abort sites set the typed fault channel alongside
    the sentinel). -/
theorem StateBounded.with_abort {s : State} (h : StateBounded s)
    (e : Option Nat) (v : Option VmError) :
    StateBounded { s with exitCode := e, vmError := v } :=
  { regs_lt := h.regs_lt, stack_r10 := h.stack_r10
    stack_depth := h.stack_depth, frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt, heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le, mem_lt := h.mem_lt }

/-- Arms `{ s with mem := m', pc := pc' }` (stores), given the new
    memory is byte-bounded. -/
theorem StateBounded.with_mem {s : State} (h : StateBounded s)
    {m' : Mem} (hm : ∀ a, m' a < 256) (pc' : Nat) :
    StateBounded { s with mem := m', pc := pc' } :=
  { regs_lt := h.regs_lt, stack_r10 := h.stack_r10
    stack_depth := h.stack_depth, frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt, heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le, mem_lt := hm }

/-! ## Structural syscall sweeps

No syscall touches the call stack or the CU budget; these two equalities
let the stack/budget invariant components carry through the `.call` arm
for every syscall at once (the r10 analog, `execSyscall_preserves_r10`,
already exists in `Execute.lean`). -/

theorem execSyscall_callStack (sc : Syscall) (s : State) :
    (execSyscall sc s).callStack = s.callStack := by
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    (first | rfl | simp)

theorem execSyscall_cuBudget (sc : Syscall) (s : State) :
    (execSyscall sc s).cuBudget = s.cuBudget := by
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    (first | rfl | simp)

/-! ## Value syscall sweeps

The four invariant components a syscall can actually move: the heap bump
pointer (`sol_alloc_free_` only, capped by `allocFreeStep`), the return
data (`sol_set_return_data` only, capped at 1024), r0 (every syscall, to
a status code / length / address — all bounded), and memory (bulk writes
— all byte-reduced). -/

/-- `execTryFind` helper in the `execTryFind_preserves_r10` style: it
    never touches the heap pointer (in either match arm). -/
@[simp] theorem _root_.SVM.SBPF.Pda.execTryFind_heapNext (s : State) :
    (Pda.execTryFind s).heapNext = s.heapNext := by
  simp only [Pda.execTryFind]
  refine State.guardRead_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  split
  · refine State.guardWrite_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
    refine State.guardWrite_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
    rfl
  · rfl

/-- `execTryFind` never touches the return data. -/
@[simp] theorem _root_.SVM.SBPF.Pda.execTryFind_returnData (s : State) :
    (Pda.execTryFind s).returnData = s.returnData := by
  simp only [Pda.execTryFind]
  refine State.guardRead_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  split
  · refine State.guardWrite_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
    refine State.guardWrite_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
    rfl
  · rfl

theorem execSyscall_heapNext_le (sc : Syscall) (s : State)
    (h : s.heapNext ≤ 0x300008000) :
    (execSyscall sc s).heapNext ≤ 0x300008000 := by
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    (first | exact h | omega | (simp; omega))

theorem execSyscall_returnData_le (sc : Syscall) (s : State)
    (h : s.returnData.size ≤ 1024) :
    (execSyscall sc s).returnData.size ≤ 1024 := by
  cases sc <;> simp [execSyscall, commitOptional, MAX_RETURN_DATA] <;>
    (repeat' split) <;> (first | exact h | omega | (simp; omega))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 65536 in
theorem execSyscall_regs_lt (sc : Syscall) (s : State) (hb : StateBounded s) :
    ∀ r, (execSyscall sc s).regs.get r < U64_MODULUS := by
  have h1 := hb.returnData_le
  have h2 := hb.cuBudget_lt
  have h3 := hb.heapNext_le
  intro r
  -- `simp only` over the explicit exec-def roster: keeps `RegFile.get`/
  -- `set` FOLDED (a full `simp` unfolds them and `repeat' split` then
  -- cases on `r` itself), and keeps the `sysvarBuffer` eval lemmas and
  -- 20 KiB buffer literals OUT of the proof term (the kernel
  -- deep-recursion hazard — see the H7 notes in `SysvarData.lean`).
  cases sc <;>
    simp only [execSyscall, commitOptional,
          State.guardRead, State.guardWrite, State.accessFault,
          Logging.execLog, Logging.execLogPubkey, Logging.execLog64,
          Logging.execLogComputeUnits,
          MemOps.execCopy, MemOps.execSet, MemOps.execCmp,
          Secp256k1.exec, Curve25519.execValidate, Curve25519.execGroupOp,
          Curve25519.execMSM, Bls12_381.execDecompress, Bls12_381.execPairing,
          AltBn128.execGroupOp, AltBn128.execCompression, BigModExp.exec,
          Cpi.exec,
          Sysvar.execClock,
          Sysvar.execLastRestartSlot, Sysvar.execFees,
          Sysvar.execEpochRewards, Misc.execGetSysvar, Sysvar.execEpochStake,
          Sysvar.zeroFillR1, ReturnData.execSet, ReturnData.execGet,
          Abort.execAbort, Abort.execPanic, Misc.execAllocFree,
          Misc.allocFreeStep, Misc.execRemainingComputeUnits,
          Misc.execGetStackHeight, Misc.execProcessedSibling,
          Misc.execUnknown] <;>
    (repeat' split) <;>
    (first
      | exact hb.regs_lt r
      | exact RegFile.set_get_lt hb.regs_lt (by decide) _ r
      | exact RegFile.set_get_lt hb.regs_lt
          (by simp only [U64_MODULUS] at h1 h2 h3 ⊢; omega) _ r
      -- `sol_log_data` is kept folded (its recursive `guardSlices` walk does
      -- not unfold under `simp only`): close it via the descriptor-walk
      -- register lemma — the result is `s.regs` (fault) or `set .r0 0`.
      | exact Logging.execLogData_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      -- hash family (sha256/512/keccak/blake3): kept OUT of the roster (digest
      -- term stays folded); close each via its per-hash regs lemma — a cheap
      -- head-match on the folded `exec`, no metavars in this 1M-heartbeat sweep.
      | exact Sha256_exec_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      | exact Sha512_exec_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      | exact Keccak256_exec_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      | exact Blake3_exec_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      -- poseidon: `commitOptional` body sets r0 to 0 (some) or 1 (none).
      | exact Poseidon_exec_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
          (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      -- PDA create: `guardRead` (program_id) wrapping `guardedCommit`; folded
      -- exec, regs = s.regs / set .r0 {0,1}.
      | exact Pda_execCreate_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
          (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      -- PDA try-find: input guards wrapping a some/none body; regs = s.regs /
      -- set .r0 {0,1}.
      | exact Pda_execTryFind_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
          (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      -- rent / epoch_schedule (de-simp'd, out of roster): folded exec, set .r0 0.
      | exact Sysvar.execRent_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r)
      | exact Sysvar.execEpochSchedule_regs_of_k (motive := fun rf => rf.get r < U64_MODULUS)
          s (hb.regs_lt r) (RegFile.set_get_lt hb.regs_lt (by decide) .r0 r))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 65536 in
theorem execSyscall_mem_lt (sc : Syscall) (s : State) (hb : StateBounded s) :
    ∀ a, (execSyscall sc s).mem a < 256 := by
  intro a
  -- Same `simp only` roster discipline as `execSyscall_regs_lt`.
  -- Leaf families: unchanged memory (IH); `writeBytes` bulk outputs
  -- (folded — closed by `writeBytes_lt`); `writeU32` (memcmp's out
  -- write — defeq `writeByWidth .word`); and the function-coerced
  -- lambda writes, opened by `Mem.read_coe` + split, whose branches
  -- are literals, `% 256` reads, `ByteArray` bytes, or the old memory.
  cases sc <;>
    simp only [execSyscall, commitOptional,
          State.guardRead, State.guardWrite, State.accessFault,
          Logging.execLog, Logging.execLogPubkey, Logging.execLog64,
          Logging.execLogComputeUnits,
          MemOps.execCopy, MemOps.execSet, MemOps.execCmp,
          Secp256k1.exec, Curve25519.execValidate, Curve25519.execGroupOp,
          Curve25519.execMSM, Bls12_381.execDecompress, Bls12_381.execPairing,
          AltBn128.execGroupOp, AltBn128.execCompression, BigModExp.exec,
          Cpi.exec,
          Sysvar.execClock,
          Sysvar.execLastRestartSlot, Sysvar.execFees,
          Sysvar.execEpochRewards, Misc.execGetSysvar, Sysvar.execEpochStake,
          Sysvar.zeroFillR1, ReturnData.execSet, ReturnData.execGet,
          Abort.execAbort, Abort.execPanic, Misc.execAllocFree,
          Misc.allocFreeStep, Misc.execRemainingComputeUnits,
          Misc.execGetStackHeight, Misc.execProcessedSibling,
          Misc.execUnknown] <;>
    (repeat' split) <;>
    (first
      | exact hb.mem_lt a
      | exact hb.mem_lt _
      -- `sol_log_data` stays folded (recursive `guardSlices`): it never
      -- writes memory, so rewrite `(execLogData s).mem` to `s.mem`.
      | (rw [Logging.execLogData_mem]; exact hb.mem_lt a)
      -- hash family (kept out of the roster, see regs_lt): per-hash closer,
      -- a cheap head-match on the folded `exec` (no metavars in this sweep).
      | exact Sha256_exec_mem_lt s hb.mem_lt a
      | exact Sha512_exec_mem_lt s hb.mem_lt a
      | exact Keccak256_exec_mem_lt s hb.mem_lt a
      | exact Blake3_exec_mem_lt s hb.mem_lt a
      | exact Poseidon_exec_mem_lt s hb.mem_lt a
      | exact Pda_execCreate_mem_lt s hb.mem_lt a
      | exact Pda_execTryFind_mem_lt s hb.mem_lt a
      -- rent / epoch_schedule (de-simp'd, out of roster): head-match on the
      -- folded exec; its lambda write is byte-bounded.
      | exact execRent_mem_lt s hb.mem_lt a
      | exact execEpochSchedule_mem_lt s hb.mem_lt a
      | exact writeBytes_lt _ _ _ _ hb.mem_lt a
      | exact writeBytes_lt _ _ _ _ hb.mem_lt _
      | exact writeByWidth_lt _ _ _ .word hb.mem_lt a
      | omega
      | exact Nat.mod_lt _ (by decide)
      | exact byte_toNat_lt _
      -- Function-coerced lambda writes: `apply` the overlay-agnostic
      -- constructor-literal bound, then peel the if-chain by repeated
      -- `apply ite_lt` (defeq-through-the-redex — see its docstring),
      -- closing branches as literals / `% 256` reads / `ByteArray`
      -- bytes / fallthrough to the old memory or a `writeBytes`.
      | (apply Mem.read_mk_lt
         intro x
         repeat
           first
             | omega
             | exact Nat.mod_lt _ (by decide)
             | exact byte_toNat_lt _
             | exact hb.mem_lt _
             | exact writeBytes_lt _ _ _ _ hb.mem_lt _
             | apply ite_lt))

/-- `n >>> k ≤ n` (right shifts only shrink). -/
theorem shiftRight_le' (n k : Nat) : n >>> k ≤ n := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _

/-! ## Step preservation -/

set_option maxHeartbeats 1000000 in
/-- THE preservation theorem (audit L5 + L3): one `step` keeps the state
    bounded. The three stack-touching arms (`call`/`call_local`/`exit`)
    are bespoke; every other arm is a record update matching one of the
    `with_*` shapes plus an arithmetic bound. -/
theorem step_bounded (insn : Insn) {s : State} (h : StateBounded s) :
    StateBounded (step insn s) := by
  cases insn
  case call sc =>
    -- `{ execSyscall sc s with pc := _, cuConsumed := _ }`: every
    -- component comes from one of the syscall sweeps.
    simp only [step]
    exact
      { regs_lt := execSyscall_regs_lt sc s h
        stack_r10 := by
          show StackR10WF (execSyscall sc s).callStack
            (execSyscall sc s).regs.r10
          rw [execSyscall_callStack, execSyscall_preserves_r10]
          exact h.stack_r10
        stack_depth := by
          show (execSyscall sc s).callStack.length ≤ _
          rw [execSyscall_callStack]; exact h.stack_depth
        frames_lt := by
          show ∀ f ∈ (execSyscall sc s).callStack, _
          rw [execSyscall_callStack]; exact h.frames_lt
        cuBudget_lt := by
          show (execSyscall sc s).cuBudget < _
          rw [execSyscall_cuBudget]; exact h.cuBudget_lt
        heapNext_le := execSyscall_heapNext_le sc s h.heapNext_le
        returnData_le := execSyscall_returnData_le sc s h.returnData_le
        mem_lt := execSyscall_mem_lt sc s h }
  case call_local target =>
    simp only [step]
    split
    · -- depth-64 guard tripped: fail-closed abort.
      exact h.with_abort _ _
    · next hdepth =>
      -- Push: frame saves the (bounded) registers; r10 climbs one frame,
      -- re-establishing the discipline at depth+1.
      have hr10 := h.r10_eq
      have hd := h.stack_depth
      refine
        { regs_lt := ?_
          stack_r10 := ⟨rfl, h.stack_r10⟩
          stack_depth := ?_
          frames_lt := ?_
          cuBudget_lt := h.cuBudget_lt
          heapNext_le := h.heapNext_le
          returnData_le := h.returnData_le
          mem_lt := h.mem_lt }
      · intro r
        cases r <;>
          first
            | exact h.regs_lt .r0 | exact h.regs_lt .r1 | exact h.regs_lt .r2
            | exact h.regs_lt .r3 | exact h.regs_lt .r4 | exact h.regs_lt .r5
            | exact h.regs_lt .r6 | exact h.regs_lt .r7 | exact h.regs_lt .r8
            | exact h.regs_lt .r9
            | (show s.regs.r10 + 0x1000 < U64_MODULUS
               simp only [STACK_START, MAX_CALL_DEPTH, U64_MODULUS] at hr10 hd ⊢
               omega)
      · show (_ :: s.callStack).length ≤ MAX_CALL_DEPTH
        simp only [List.length_cons, MAX_CALL_DEPTH] at hdepth ⊢
        omega
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact ⟨h.regs_lt .r6, h.regs_lt .r7, h.regs_lt .r8, h.regs_lt .r9⟩
        · exact h.frames_lt f hf'
  case exit =>
    simp only [step]
    split
    · next frame rest heq =>
      -- Pop: r10 restores to the top frame's saved pointer, which the
      -- discipline pins one frame down; r6-r9 restore to saved values
      -- bounded by `frames_lt`.
      have hfr := h.frames_lt frame (by rw [heq]; exact List.mem_cons_self ..)
      have hwf : StackR10WF (frame :: rest) s.regs.r10 := heq ▸ h.stack_r10
      obtain ⟨-, hrest⟩ := hwf
      have hdep : rest.length ≤ MAX_CALL_DEPTH := by
        have hl := h.stack_depth
        rw [heq] at hl
        simp only [List.length_cons] at hl
        omega
      have hr10' := hrest.r10_eq
      refine
        { regs_lt := ?_
          stack_r10 := hrest
          stack_depth := hdep
          frames_lt := ?_
          cuBudget_lt := h.cuBudget_lt
          heapNext_le := h.heapNext_le
          returnData_le := h.returnData_le
          mem_lt := h.mem_lt }
      · intro r
        cases r <;>
          first
            | exact h.regs_lt .r0 | exact h.regs_lt .r1 | exact h.regs_lt .r2
            | exact h.regs_lt .r3 | exact h.regs_lt .r4 | exact h.regs_lt .r5
            | exact hfr.1 | exact hfr.2.1 | exact hfr.2.2.1 | exact hfr.2.2.2
            | (show frame.savedR10 < U64_MODULUS
               simp only [STACK_START, MAX_CALL_DEPTH, U64_MODULUS]
                 at hr10' hdep ⊢
               omega)
      · intro f hf
        exact h.frames_lt f (by rw [heq]; exact List.mem_cons_of_mem _ hf)
    · -- Empty stack: program exit (sets only exitCode).
      exact h.with_exitCode _
  all_goals
    simp only [step] <;> (repeat' split) <;>
      first
        | exact h.with_abort _ _
        | exact h.with_exitCode _
        | exact h.with_pc _
        | exact h.with_mem (writeByWidth_lt _ _ _ _ h.mem_lt) _
        | exact h.with_set_reg (toU64_lt _) _
        | exact h.with_set_reg (readByWidth_lt _ _ _) _
        | exact h.with_set_reg (wrapAdd_lt _ _) _
        | exact h.with_set_reg (wrapSub_lt _ _) _
        | exact h.with_set_reg (wrapMul_lt _ _) _
        | exact h.with_set_reg (wrapNeg_lt _) _
        | exact h.with_set_reg (wrapAdd32_lt _ _) _
        | exact h.with_set_reg (wrapSub32_lt _ _) _
        | exact h.with_set_reg (wrapMul32_lt _ _) _
        | exact h.with_set_reg (wrapNeg32_lt _) _
        | exact h.with_set_reg (resolveSrc_lt h.regs_lt _) _
        | exact h.with_set_reg (Nat.mod_lt _ (by decide)) _
        | exact h.with_set_reg
            (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (h.regs_lt _)) _
        | exact h.with_set_reg
            (Nat.lt_of_le_of_lt (shiftRight_le' _ _) (h.regs_lt _)) _
        | exact h.with_set_reg
            (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)) _
        | exact h.with_set_reg
            (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.mod_le _ _)
              (Nat.mod_lt _ (by decide))) (by decide)) _
        | exact h.with_set_reg
            (Nat.lt_trans (Nat.lt_of_le_of_lt (shiftRight_le' _ _)
              (Nat.mod_lt _ (by decide))) (by decide)) _

/-- `chargeCu` only moves the consumed meter — every invariant component
    carries. -/
theorem chargeCu_bounded {s : State} (h : StateBounded s) :
    StateBounded (chargeCu s) :=
  { regs_lt := h.regs_lt, stack_r10 := h.stack_r10
    stack_depth := h.stack_depth, frames_lt := h.frames_lt
    cuBudget_lt := h.cuBudget_lt, heapNext_le := h.heapNext_le
    returnData_le := h.returnData_le, mem_lt := h.mem_lt }

/-- THE multi-step preservation theorem: the proof-side executor keeps
    every reachable state bounded, for any program and any fuel. -/
theorem executeFn_bounded (fetch : Nat → Option Insn) {s : State}
    (h : StateBounded s) (fuel : Nat) :
    StateBounded (executeFn fetch s fuel) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel' ih =>
    rw [executeFn]
    split
    · exact h                         -- already exited
    · split
      · exact h                       -- budget exhausted: halt as-is
      · split
        · exact h.with_abort _ _      -- invalid PC: fail closed
        · exact ih (chargeCu_bounded (step_bounded _ h))

/-! ## The L5 / L3 closes -/

/-- L5 (audit): every register of every state the executor can reach is
    a real u64. In particular the unsigned compares
    (`jgt`/`jge`/`jlt`/`jle`), which compare RAW `Nat` register values,
    are faithful u64 compares on every reachable state. -/
theorem executeFn_regs_lt (fetch : Nat → Option Insn) {s : State}
    (h : StateBounded s) (fuel : Nat) :
    ∀ r, (executeFn fetch s fuel).regs.get r < 2 ^ 64 :=
  (executeFn_bounded fetch h fuel).regs_lt

/-- L3 (audit): a byte-cell claim `s.mem a = v` with `v ≥ 256` is FALSE
    of every bounded state — real cells hold real bytes. So a
    `memByteIs a v` atom with a non-canonical `v` is unsatisfiable
    against any reachable state's memory: the raw-valued `singletonMem`
    definition cannot be exploited on the reachable fragment. (This is
    the invariant-side fence; canonicalising `singletonMem` itself was
    attempted and reverted — it ripples `< 256` hypotheses through the
    byte-cell specs into the H8 byte-demotion base.) -/
theorem mem_byte_canonical {s : State} (h : StateBounded s) {a v : Nat}
    (hv : 256 ≤ v) : s.mem a ≠ v := by
  intro he
  have := h.mem_lt a
  omega

/-! ## Base cases -/

/-- `Execute.initState` is bounded, given bounded inputs (the input
    address and CU budget are caller-supplied; real callers pass region
    addresses and budgets far below 2^64). -/
theorem initState_bounded (inputAddr : Nat) (mem : Mem)
    (regions : RegionTable) (cuBudget : Nat := 200000)
    (haddr : inputAddr < U64_MODULUS)
    (hcu : cuBudget < U64_MODULUS)
    (hmem : ∀ a, mem a < 256) :
    StateBounded (initState inputAddr mem regions cuBudget) :=
  { regs_lt := by
      intro r
      cases r <;> simp [initState, U64_MODULUS] <;> first
        | exact haddr
        | decide
    stack_r10 := by simp [initState, StackR10WF]
    stack_depth := by simp [initState]
    frames_lt := by simp [initState]
    cuBudget_lt := hcu
    heapNext_le := by simp [initState]
    returnData_le := by simp [initState]
    mem_lt := hmem }

/-- The runner's initial state (diff path and `run`/`runElf`) is bounded
    for any budget `< 2^64` (the FFI passes a u64, so this is every real
    run). -/
theorem initialState_bounded (cfg : Runner.RunConfig)
    (hcu : cfg.cuBudget < U64_MODULUS) :
    StateBounded (Runner.initialState cfg) :=
  { regs_lt := by
      intro r
      cases r <;> simp [Runner.initialState, U64_MODULUS] <;> decide
    stack_r10 := by simp [Runner.initialState, StackR10WF]
    stack_depth := by simp [Runner.initialState]
    frames_lt := by simp [Runner.initialState]
    cuBudget_lt := hcu
    heapNext_le := by simp [Runner.initialState]
    returnData_le := by simp [Runner.initialState]
    mem_lt := loadInput_lt cfg.input }

end SVM.SBPF
