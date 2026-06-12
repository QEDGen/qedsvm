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
