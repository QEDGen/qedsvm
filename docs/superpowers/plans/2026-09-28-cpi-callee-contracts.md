# CPI Callee Contracts Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A Lean theorem that the runner, executing `sbpfv3_cpi_writer.so` with the pinned callee `sbpfv3_cpi_writer_callee.so`, exits 0 with account `data[0] = 42` and heap+200 = 43, for every state satisfying the caller's precondition and the side conditions.

**Architecture:** Factor the runner's invoke step into `Runner.stepCpi`, define the callee relation `Cpi.runnerCallee` from it, and prove the runner's run through an invoke is prefix, `Cpi.Transitions`, suffix. Prove contracts (`writesWithin`/`writesOnly`) about `runnerCallee` restricted by a caller-memory invariant: a generic write-back frame from `commitCallee`, and the concrete callee's narrow frame and value from its lifted path plus serialization read lemmas. Instantiate the existing `Sbpfv3CpiWriterLiftedSuccess_cpi_path`.

**Tech Stack:** Lean 4 (lake), qedsvm SVM library, qedlift (Rust) for the callee lift, Mollusk differential tests.

**Spec:** `docs/superpowers/specs/2026-09-28-cpi-callee-contracts-design.md`

## Global Constraints

- New theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no new `axiom`.
- Native-program callees are excluded by hypothesis, never modelled here.
- Serialization proofs keep `MAX_PERMITTED_DATA_INCREASE` padding symbolic; a module that takes over a minute to build is treated as a bug.
- Runner refactors are definitional: existing `RunnerBridge`/`BoundedCpi` proofs and all Mollusk differential tests must stay green unchanged in behavior.
- Public docs use no em dashes.
- Commit trailer: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## Design refinements over the spec (found while planning)

1. The runner charges one step unit on top of the CPI result: after an invoke the caller state is `chargeCu (cpiCallNextState …)`. `runnerCallee` therefore relates `chargeCu (stepCpi …)` to `applyResult s r` (the extra unit lands in `r.cuConsumed`).
2. `writesOnly`/`writesWithin` constrain only successful results (`r.code = 0`). Failed results are rolled back by `applyResult`, so `cpiTriple_of_writes` still holds; and a callee that ran out of fuel or faulted never needs a frame.
3. The callee's program id, account descriptors and account block are caller memory, not part of the relation. Contracts are proved for `Cpi.restrict (runnerCallee …) inv`, where `inv` states those memory facts; the end-to-end proof supplies `inv` at the invoke state from the prefix post and the frame.

## File Structure

- `qedsvm-rs/tests/fixtures/build_sbpfv3_static_path.py`: add the pinned callee.
- `qedsvm-rs/tests/fixtures/sbpfv3_cpi_writer_callee.so` (+ `.pcs`), manifest entry.
- `examples/lean/Generated/Sbpfv3CpiWriterCalleeLifted.lean`: callee path proof.
- `SVM/SBPF/CpiContract.lean`: success-only `writesWithin`/`writesOnly`, `restrict`.
- `SVM/SBPF/Runner.lean`: extract `stepCpi` (definitional).
- `SVM/SBPF/CpiRunner.lean` (new): `runnerCallee`, transition lemma, run decomposition, generic frame.
- `SVM/SBPF/CpiSerialization.lean` (new): input-serialization and write-back read lemmas.
- `examples/lean/CpiWriterEndToEnd.lean` (new): callee invariant, callee contract, end-to-end theorem, sanity run.
- `docs/COVERAGE.md`: runner bridge and end-to-end result.

---

### Task 1: Pinned callee fixture and its path proof

**Files:**
- Modify: `qedsvm-rs/tests/fixtures/build_sbpfv3_static_path.py`
- Create: `qedsvm-rs/tests/fixtures/sbpfv3_cpi_writer_callee.so`, `qedsvm-rs/tests/fixtures/sbpfv3_cpi_writer_callee.pcs`
- Modify: `qedsvm-rs/tests/fixtures/sbpfv3_fixtures.sha256`, `qedsvm-rs/tests/fixtures/README.md`, `qedsvm-rs/tests/diff_mollusk.rs`, `qedsvm-rs/qedlift/tests/public_api.rs`, `lakefile.lean`
- Create: `examples/lean/Generated/Sbpfv3CpiWriterCalleeLifted.lean`

**Interfaces:**
- Produces: `Examples.Lifted.Sbpfv3CpiWriterCalleeLifted.Sbpfv3CpiWriterCalleeLifted_lifted_spec` (a `cuTripleWithinMem 3 0 0 3 …` over pcs 0..2, exit at pc 3) and `…_v3_elf_text`, `…Elf`.

- [ ] **Step 1: Add the callee to the builder.** Append to `build_sbpfv3_static_path.py`:

```python
# CPI writer callee: data[0] of its first account := 42, then success.
CPI_WRITER_CALLEE_TEXT = bytes.fromhex(
    "b70200002a000000"  # mov64 r2, 42
    "7321600000000000"  # stxb [r1+96], r2
    "b700000000000000"  # mov64 r0, 0
    "9500000000000000"  # exit
)
write_elf("sbpfv3_cpi_writer_callee.so", CPI_WRITER_CALLEE_TEXT)
```

Run: `cd qedsvm-rs/tests/fixtures && python3 build_sbpfv3_static_path.py && printf '0\n1\n2\n3\n' > sbpfv3_cpi_writer_callee.pcs && shasum -a 256 sbpfv3_*.so > sbpfv3_fixtures.sha256`. Expected: existing fixture hashes unchanged in the manifest diff, one new line.

- [ ] **Step 2: Use it in the writer differential.** In `sbpfv3_cpi_writer_commit_and_rollback_match_mollusk`, add `const SBPFV3_CPI_WRITER_CALLEE_SO: &[u8] = include_bytes!("fixtures/sbpfv3_cpi_writer_callee.so");` next to `SBPFV3_CPI_WRITER_SO` and use it as the callee when `exit_code == 0`:

```rust
let callee: Vec<u8> = if exit_code == 0 {
    SBPFV3_CPI_WRITER_CALLEE_SO.to_vec()
} else {
    v3_elf(&[
        v3_insn(0xb7, 2, 0, 0, 42),
        v3_insn(0x73, 1, 2, 96, 0),
        v3_insn(0xb7, 0, 0, 0, exit_code),
        v3_insn(0x95, 0, 0, 0, 0),
    ])
};
```

Run: `cd qedsvm-rs && cargo test -q --features diff-mollusk --test diff_mollusk sbpfv3_cpi_writer`. Expected: PASS.

- [ ] **Step 3: Lift the callee and pin it.** Run from `qedsvm-rs`: `cargo run -q -p qedlift --bin qedlift -- --so tests/fixtures/sbpfv3_cpi_writer_callee.so --trace tests/fixtures/sbpfv3_cpi_writer_callee.pcs --module Sbpfv3CpiWriterCalleeLifted --output ../examples/lean/Generated/Sbpfv3CpiWriterCalleeLifted.lean`. Add `` `Generated.Sbpfv3CpiWriterCalleeLifted, `` to the `ExamplesCpi` roots in `lakefile.lean`. Add to `public_api.rs`:

```rust
#[test]
fn lifts_the_cpi_writer_callee() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_cpi_writer_callee.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let result = lifter.lift(LiftOptions {
        trace: Some(&[0, 1, 2, 3]),
        module_override: Some("Sbpfv3CpiWriterCalleeLifted".to_string()),
        ..LiftOptions::default()
    })?;
    assert_eq!(
        result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiWriterCalleeLifted.lean")
    );
    Ok(())
}
```

Run: `lake build Generated.Sbpfv3CpiWriterCalleeLifted` and `cd qedsvm-rs && cargo test -q -p qedlift --test public_api lifts_the_cpi_writer_callee`. Expected: both pass; the theorem's post contains `(effectiveAddr baseAddr 96 ↦ₘ toU64 42 % 256)` (or the emitter's equivalent byte form) and `(.r0 ↦ᵣ toU64 0)`.

- [ ] **Step 4: Document and commit.** Add a README fixture paragraph (source line, SHA-256 in manifest, role as the pinned success callee). Commit: `feat(sbpfv3): pin the CPI writer callee and its path proof`.

---

### Task 2: Success-only write contracts and restriction

**Files:**
- Modify: `SVM/SBPF/CpiContract.lean`

**Interfaces:**
- Produces:
  - `Cpi.writesWithin (callee : CalleeSemantics) (fp : Nat → Prop) : Prop := ∀ s r, callee s r → r.code = 0 → ∀ a, ¬ fp a → r.mem a = s.mem a`
  - `Cpi.writesOnly callee addrs := writesWithin callee (· ∈ addrs)` (definitional; same name, same argument order)
  - `Cpi.restrict (callee : CalleeSemantics) (inv : State → Prop) : CalleeSemantics := fun s r => inv s ∧ callee s r`
  - `Cpi.writesWithin_mono : (∀ a, fp a → fp' a) → writesWithin c fp → writesWithin c fp'`
  - `Cpi.transitions_restrict : inv s → Transitions c s s' → Transitions (restrict c inv) s s'`
  - `cpiTriple_of_writes` unchanged in statement.

- [ ] **Step 1: Redefine.** Replace `writesOnly`'s body with the `writesWithin` special case above and add the new definitions and two lemmas.

- [ ] **Step 2: Re-prove `cpiTriple_of_writes`.** In the frame-memory case, split on `r.code = 0`: success uses `hW s r hCallee hcode a hnot`; failure rewrites `applyResult_mem_failure` so memory is `s.mem` directly.

- [ ] **Step 3: Verify.** Run: `lake build SVM.SBPF.CpiContract Generated.Sbpfv3CpiWriterLiftedSuccess Generated.Sbpfv3CpiWriterLiftedRollback Generated.Sbpfv3CpiCallerLiftedSuccess`. Expected: all build (the generated modules' text is unchanged).

- [ ] **Step 4: Commit.** `feat(cpi): success-only write frames and contract restriction`.

---

### Task 3: Runner invoke step and `runnerCallee`

**Files:**
- Modify: `SVM/SBPF/Runner.lean` (extract `stepCpi` from `executeFnCpiWithFuel`)
- Create: `SVM/SBPF/CpiRunner.lean`; Modify: `SVM/SBPF.lean` (import)

**Interfaces:**
- Produces:
  - `Runner.stepCpi (registry : Nat → Option ByteArray) (subRun : (Nat → Option Insn) → State → Nat → State × Nat) (s : State) (fuel' : Nat) (insn : Insn) : State`: exactly the `s'` of `executeFnCpiWithFuel` (both invoke arms, `step insn s` otherwise), with the callee's sub-run supplied as `subRun`. `executeFnCpiWithFuel` uses it: `… | some insn => … executeFnCpiWithFuel registry fetch (chargeCu (stepCpi registry (executeFnCpiWithFuel registry) s fuel' insn)) fuel'` (the recursive call inside `subRun` is at `fuel'`, so recursion stays structural).
  - `Cpi.runnerCallee (registry) (sc : Syscall) : CalleeSemantics := fun s r => ∃ fuel', chargeCu (Runner.stepCpi registry (Runner.executeFnCpiWithFuel registry) s fuel' (.call sc)) = applyResult s r`
  - `Cpi.stepCpi_is_transition (registry subRun s fuel') (sc) (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c) : ∃ r, chargeCu (Runner.stepCpi registry subRun s fuel' (.call sc)) = applyResult s r`

- [ ] **Step 1: Extract `stepCpi`.** Move the `let s' : State := match insn with …` block (including the `runCallee` closure) into `stepCpi`, replacing the closure's `executeFnCpiWithFuel registry (fetchFromArray calleeInsns) subS fuel'` with `subRun (fetchFromArray calleeInsns) subS fuel'`. Define `stepCpi` before `executeFnCpiWithFuel`; the latter passes `executeFnCpiWithFuel registry` as `subRun`, called only at `fuel'`, so termination stays structural on `fuel`.

- [ ] **Step 2: Keep existing proofs green.** Add `stepCpi` to the unfold lists in `RunnerBridge.executeFnCpi_eq_executeFn_of_no_cpi` and `BoundedCpi` where they unfold `executeFnCpiWithFuel`. Run: `lake build SVM.SBPF.RunnerBridge SVM.SBPF.BoundedCpi SVM.SBPF.RunnerTests`. Expected: PASS.

- [ ] **Step 3: Prove `stepCpi_is_transition`.** Unfold `stepCpi` and `cpiCallNextState`; for each branch give the witness:
  - depth / aliasing / unregistered / `runCallee = none`: `⟨1, s.mem, s.log, s.returnData, s.returnDataProgId, 1⟩` (the `1` in `cuConsumed` is `chargeCu`'s unit; `applyResult` adds `Cpi.cu`).
  - native: `⟨nr.r0, nr.mem, s.log, s.returnData, s.returnDataProgId, nr.cu + 1⟩`.
  - BPF: `⟨subFinal.exitCode.getD 1, newMem, subFinal.log, subFinal.returnData, subFinal.returnDataProgId, subFinal.cuConsumed + 1⟩`.
  Each case closes by `simp [applyResult, chargeCu]` plus `State` extensionality on the updated fields (`pc`, `regs`, `mem`, `log`, `returnData`, `returnDataProgId`, `cuConsumed`). Check `chargeCu`'s definition first and adjust the unit if it charges differently.

- [ ] **Step 4: Sanity check.** In `SVM/SBPF/RunnerTests.lean` add an `example` running `Runner.runForExit cpiCallerBytes { programRegistry := cpiV3Registry }` unchanged (existing `= some 42` still decides) to show the refactor kept runner behavior. Run the full differential: `cd qedsvm-rs && cargo test -q --features diff-mollusk --test diff_mollusk`. Expected: all pass.

- [ ] **Step 5: Commit.** `feat(cpi): runner invoke step as a CPI transition`.

---

### Task 4: Runner runs through an invoke

**Files:**
- Modify: `SVM/SBPF/CpiRunner.lean`

**Interfaces:**
- Consumes: `Runner.stepCpi`, `Cpi.runnerCallee`, `Cpi.cpiPathWithinMem`.
- Produces:
  - `CodeReq.restrictFetch (cr : CodeReq) (fetch) : Nat → Option Insn := fun a => (cr a).bind fun i => if fetch a = some i then some i else none`
  - `executeFn_agree_of_restrict`: if `f' a = some i → f a = some i` and `(executeFn f' s k).exitCode = none` then `executeFn f s k = executeFn f' s k`.
  - `runner_prefix`: for a CPI-free `f'` agreeing with `fetch` on the first `k` steps (as above), `executeFnCpiWithFuel registry fetch s (k + m) = executeFnCpiWithFuel registry fetch (executeFn fetch s k) m`.
  - `runner_invoke`: if `sI.exitCode = none`, `sI.cuConsumed ≤ sI.cuBudget`, `fetch sI.pc = some (.call sc)` then `executeFnCpiWithFuel registry fetch sI (m + 1) = executeFnCpiWithFuel registry fetch (chargeCu (Runner.stepCpi registry (Runner.executeFnCpiWithFuel registry) sI m (.call sc))) m`.
  - `Cpi.runner_cpiPath`: from `cpiPathWithinMem N1 M1 entry invokePc N2 M2 exit_ cr1 cr2 P Post rr1 rr2 sc (restrict (runnerCallee registry sc) inv) G`, a frame `R`, `(P ** R).holdsFor s`, entry/budget/region hypotheses, `inv` derivable at the invoke state (`hInv : ∀ sI, (Q ** R).holdsFor sI → inv sI` with `Q` the prefix post), the guard for the runner's result, and fuel `F ≥ N1 + 1 + N2`: there is a result `r` with `G r → (Post r ** R).holdsFor` of the runner's state after `N1`-prefix, invoke and suffix steps, and that state's `pc = exit_`.

- [ ] **Step 1: Write the restriction agreement lemma** by induction on `k`, unfolding one `executeFn` step; the `exitCode = none` hypothesis rules out the `fetch = none` fault arm under `f'`.

- [ ] **Step 2: Write `runner_prefix`** by induction on `k`, reusing the step-level argument from `executeFnCpi_eq_executeFn_of_no_cpi` (CPI-free fetch ⇒ `stepCpi … insn = step insn s`).

- [ ] **Step 3: Write `runner_invoke`** by one unfolding of `executeFnCpiWithFuel`.

- [ ] **Step 4: Assemble `runner_cpiPath`.** Apply the path theorem with `fetch' := restrictFetch (cr1.union (singleton invokePc (.call sc))) fetch` for the prefix and `restrictFetch cr2 fetch` for the suffix (both CPI-free except the invoke, which `runner_invoke` handles). The transition fact comes from `stepCpi_is_transition` plus `hInv`, wrapped by `transitions_restrict`.

- [ ] **Step 5: Test on the zero-account caller.** In a new `examples/lean/CpiRunnerSmoke.lean` (add to `ExamplesCpi`), instantiate `runner_cpiPath` with `Sbpfv3CpiCallerLiftedSuccess_cpi_path` and `inv := fun _ => True`, leaving the contract `hMem` as a hypothesis, and `#print axioms`. Run: `lake build CpiRunnerSmoke`. Expected: builds, standard axioms only.

- [ ] **Step 6: Commit.** `feat(cpi): runner runs through an invoke via cpi paths`.

---

### Task 5: Serialization read lemmas

**Files:**
- Create: `SVM/SBPF/CpiSerialization.lean`; Modify: `SVM/SBPF.lean`

**Interfaces:**
- Produces:
  - `Runner.buildAcctSlots_single (p) : buildAcctSlots [p] = [{ parsed := p, dupOf? := none, blockOff := 8 }]`
  - `Runner.buildCpiSubInputN_first_data (p) (pid ix) (i) (hi : i < p.data.size) (hsz : p.key.size = 32 ∧ p.owner.size = 32) : (buildCpiSubInputN [slot p] pid ix).get! (8 + CPI_BLOCK_DATA_OFFSET + i) = p.data.get! i` where `slot p` is the single slot above.
  - `Runner.loadInput_read (mem input a) (ha : a < input.size) : loadInput mem input (INPUT_START + a) = (input.get! a).toNat`
  - `Runner.loadInput_read_outside (ha : ¬ (INPUT_START ≤ a ∧ a < INPUT_START + input.size)) : loadInput mem input a = mem a`

- [ ] **Step 1: State the lemmas** above; make `emitNonDupBlock` accessible to proofs (drop `private` or add a public equation lemma `emitNonDupBlock_eq`).

- [ ] **Step 2: Prove `buildAcctSlots_single`** by `simp [buildAcctSlots, List.range, List.foldl]`.

- [ ] **Step 3: Prove the data-byte lemma** with `ByteArray.get!` over `++`: the prefix before `p.data` has size `8 + 88` (`u64ToLE` size 8, dup marker 1, flags 3, pad 4, key 32, owner 32, lamports 8, data_len 8). Use `ByteArray.size_append` and a `get!_append_left/right` pair (add them if missing, proved via `ByteArray.data` and `Array.getElem_append`). Never unfold `zeroBytes MAX_PERMITTED_DATA_INCREASE`.

- [ ] **Step 4: Prove the `loadInput` lemmas** from `loadBytesAt`'s definition (existing `loadBytesAt` read lemmas in `Runner.lean`/`Memory.lean` if present; otherwise induction on the byte list).

- [ ] **Step 5: Concrete regression.** Add `example`s evaluating the lemmas' left sides with `native_decide` on a concrete 2-byte `ParsedAcct` (data `[7, 9]`), matching `7` and `9`. Run: `lake build SVM.SBPF.CpiSerialization`. Expected: builds in well under a minute.

- [ ] **Step 6: Commit.** `feat(cpi): input serialization read lemmas`.

---

### Task 6: Write-back read lemmas and the generic frame

**Files:**
- Modify: `SVM/SBPF/CpiSerialization.lean`, `SVM/SBPF/CpiRunner.lean`

**Interfaces:**
- Produces:
  - `Runner.writeBackFootprint (slots : List AcctSlot) (a : Nat) : Prop`: `a` lies in some writable non-dup slot's data range `[p.dataPtr, p.dataPtr + p.dataLen + MAX_PERMITTED_DATA_INCREASE)`, its `data_len` slots (`p.dataLenRefAddr`, `p.dataPtr - 8`, 8 bytes each), lamports (8 bytes at `p.lamportsRefAddr`) or owner (32 bytes at `p.ownerPtr`).
  - `Runner.commitCallee_mem_outside : ¬ writeBackFootprint slots a → (commitCallee callerMem slots subFinal f).2.1 a = callerMem a`
  - `Runner.commitCallee_data (hw : p.isWritable) (hlen : post-call length = p.dataLen) (hi : i < p.dataLen) (hnoAlias : slots = [slot p]) : (commitCallee callerMem slots subFinal f).2.1 (p.dataPtr + i) = subFinal.mem (INPUT_START + 8 + CPI_BLOCK_DATA_OFFSET + i)`
  - `Cpi.invokeSlots (s : State) (sc : Syscall) : List AcctSlot`: `buildAcctSlots` of the account infos `stepCpi` parses at `s` for `sc` (same parser, PDA promotion and privilege clamp).
  - `Cpi.invokePid (s : State) (sc : Syscall) : Nat` and `Cpi.invokeNativeNone (s) (sc) : Prop`: the program id and the `Native.dispatch … = none` condition exactly as `stepCpi` computes them at `s`.
  - `Cpi.invokeFootprint (s : State) (sc : Syscall) (a : Nat) : Prop := Runner.writeBackFootprint (Cpi.invokeSlots s sc) a`
  - `Cpi.runnerCallee_writesWithin (registry sc inv) (hNative : ∀ s, inv s → Cpi.invokeNativeNone s sc) : ∀ s r, restrict (runnerCallee registry sc) inv s r → r.code = 0 → ∀ a, ¬ Cpi.invokeFootprint s sc a → r.mem a = s.mem a` (the footprint depends on `s`, so this is stated pointwise rather than as a single `writesWithin`).

- [ ] **Step 1: Prove `commitCallee_mem_outside`** by induction over the `slots.foldl`: `loadBytesAt` and `writeU64` preserve addresses outside their range (existing or new frame lemmas); the violation branches return `callerMem`.

- [ ] **Step 2: Prove `commitCallee_data`** for the single-slot case by unfolding the fold once and reading back `loadBytesAt newData p.dataPtr` at `p.dataPtr + i` (then showing the later `writeU64`s and owner write are outside by address arithmetic under explicit disjointness hypotheses on `dataPtr`, `lamportsRefAddr`, `ownerPtr`, `dataLenRefAddr`).

- [ ] **Step 3: Prove `runnerCallee_writesWithin`.** For a code-0 result the relation's witness is the BPF branch (depth/alias/unregistered/decode-failure branches have code 1; native is excluded by `hNative`), whose memory is `commitCallee`'s; conclude with `commitCallee_mem_outside`.

- [ ] **Step 4: Verify.** Run: `lake build SVM.SBPF.CpiRunner`. Expected: PASS, standard axioms (`#print axioms Cpi.runnerCallee_writesWithin` in a scratch file).

- [ ] **Step 5: Commit.** `feat(cpi): runner write-back frame for any BPF callee`.

---

### Task 7: The writer callee meets its contract

**Files:**
- Create: `examples/lean/CpiWriterEndToEnd.lean` (add to `ExamplesCpi`)

**Interfaces:**
- Consumes: Tasks 2-6, `Sbpfv3CpiWriterCalleeLifted_lifted_spec`.
- Produces:
  - `writerCalleeId : ByteArray` (32 bytes) and `writerRegistry : Nat → Option ByteArray := fun pid => if pid = (LE Nat of writerCalleeId) then some calleeElf else none`
  - `writerInv (s : State) : Prop`: the invoke state's `r1..r5` hold the `SolInstruction`/`SolAccountInfo` heap pointers the writer builds, those heap cells hold the values in `Sbpfv3CpiWriterLifted`'s prefix post, the program id bytes at `base+10360` equal `writerCalleeId`, and account 0 is writable with data length 2 at `base+96`, owner at `base+48`, lamports at `base+80`; `invokeDepth = 0`.
  - `writer_callee_contract : Cpi.writesOnly (Cpi.restrict (Cpi.runnerCallee writerRegistry .sol_invoke_signed_c) writerInv) [effectiveAddr baseAddr 96]` (quantified over `baseAddr` via `writerInv`'s base, see Step 1)
  - `writer_callee_value : ∀ s r, restrict (runnerCallee writerRegistry .sol_invoke_signed_c) writerInv s r → r.code = 0 → r.mem (base s + 96) = 42`

- [ ] **Step 1: Fix the base.** Parameterize `writerInv baseAddr` and the footprint `[effectiveAddr baseAddr 96]` by the caller's input base so it matches the path theorem's `hW` literally.

- [ ] **Step 2: The callee loads.** Prove by `native_decide`: `Elf.loadV3 calleeElf = some program` and `Decode.decodeProgram program.textBytes [] .v3 = some #[.mov64 .r2 (.imm 42), .stx .byte .r1 96 .r2, .mov64 .r0 (.imm 0), .exit]`, hence `buildCalleeVM s fuel' pid accts ix calleeElf = some (calleeInsns, subS, [slot p])` with `subS.regs.r1 = INPUT_START`, `subS.pc = 0`.

- [ ] **Step 3: The callee's precondition holds on `subS`.** From Task 5, `subS.mem (INPUT_START + 96) = p.data.get! 0 |>.toNat` and registers r0/r2 hold their initial values; build `(P_callee ** R_sub).holdsFor subS` with `baseAddr := INPUT_START`. The region side condition follows from `v3Regions`'s input region covering `INPUT_START + 96`.

- [ ] **Step 4: The callee's run.** CPI-free fetch, so the sub-run equals `executeFn` (`executeFnCpi_eq_executeFn_of_no_cpi`); apply the lifted triple for 3 steps, then one `exit` step (empty call stack ⇒ `exitCode = some r0 = some 0`). If the sub-run's fuel is below 4 the callee has not exited and the result code is `1`, so code 0 forces the full path.

- [ ] **Step 5: Narrow frame and value.** With Task 6's `commitCallee_data` and `commitCallee_mem_outside`: data byte 0 becomes 42; data byte 1, both `data_len` slots, lamports and owner are rewritten with the values the callee's frame preserved (equal to the caller's by Task 5), so every address other than `base + 96` is unchanged. Conclude both theorems.

- [ ] **Step 6: Verify.** Run: `lake build CpiWriterEndToEnd`; `#print axioms writer_callee_contract writer_callee_value`. Expected: standard axioms only.

- [ ] **Step 7: Commit.** `feat(cpi): the writer callee meets its write contract`.

---

### Task 8: End-to-end theorem, sanity run, docs

**Files:**
- Modify: `examples/lean/CpiWriterEndToEnd.lean`, `docs/COVERAGE.md`

**Interfaces:**
- Consumes: `Cpi.runner_cpiPath`, `Sbpfv3CpiWriterLiftedSuccess_cpi_path`, Task 7.
- Produces: `writer_end_to_end`: for the writer caller's decoded code (pinned via `Sbpfv3CpiWriterLifted_decode_pins`), `writerRegistry`, fuel `F ≥ 46 + 1 + 6`, and every state satisfying the caller's precondition, `writerInv`'s memory part as a frame, and the caller's path hypotheses, the runner's state after the path has `pc = 56` (the exit), `data[0] = 42` at `base + 96` and `43` at heap+200.

- [ ] **Step 1: State and prove `writer_end_to_end`** by `runner_cpiPath` with `callee := restrict (runnerCallee writerRegistry .sol_invoke_signed_c) (writerInv baseAddr)`, `hW := writer_callee_contract`, the guard `r.code = toU64 0` from `writer_callee_value`'s code-0 case, and the committed byte `Cpi.committedByte r (effectiveAddr baseAddr 96) old = 42` from `writer_callee_value`.

- [ ] **Step 2: Sanity run.** Build a concrete serialized input with `Runner.buildCpiSubInputN` for the two accounts (writable 2-byte data account owned by the callee id, the callee program account) and check by `native_decide` that `Runner.runElf writerElf { input, programRegistry := writerRegistry }` returns a state whose memory holds `42, 0` at `INPUT_START + 96` and `43` at `HEAP_START + 200`, with exit code 0.

- [ ] **Step 3: Docs.** Add to `docs/COVERAGE.md` ("V3 caller paths across a CPI") a paragraph on `runnerCallee`, `runner_cpiPath`, the generic write-back frame, and `writer_end_to_end` as the two-program result; state the remaining exclusions (natives, nested CPI in the callee, realloc, multi-account callers, multi-path callees).

- [ ] **Step 4: Gates.** Run: `lake build`, `lake build Examples`, `lake build ExamplesCpi`, `lake build SVM.SBPF.V3DecodeTests SVM.SBPF.ElfTests SVM.SBPF.RunnerTests SVM.SBPF.BoundedCpi SVM.Syscalls.CpiTests`, and from `qedsvm-rs`: `cargo test --workspace --quiet`, `cargo test --features diff-mollusk --quiet`, `cargo clippy --workspace --all-targets --all-features -- -D warnings`, `cargo fmt --all -- --check`; `git diff --check -- . ':!examples/lean/Generated'`. Expected: all pass; `#print axioms writer_end_to_end` shows the standard axioms plus the callee ELF `native_decide` pins (accepted 2026-09-28, called out in `docs/COVERAGE.md`).

- [ ] **Step 5: Commit.** `feat(cpi): prove a two-program CPI path end to end`.
