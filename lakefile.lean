import Lake
open Lake DSL System

-- qedsvm — Lean 4 reference semantics for the Solana Virtual Machine.
--
-- Pure Lean 4, no Mathlib dependency. Anything that needs Mathlib-level
-- reasoning (`Fin → α`, `BigOperators`, ring/omega over closed forms)
-- belongs in a downstream consumer, not here.
--
-- Native crypto: every cryptographic syscall goes through
-- `qedsvm-rs/lean-bridge/`, a `cargo` staticlib that pulls the exact
-- crates agave's runtime uses (`libsecp256k1 = 0.7.2` paritytech,
-- `curve25519-dalek = 4.1.3`, `sha2 = 0.10.8`, `sha3 = 0.10.8`,
-- `blake3 = 1.8.5`) and exposes them as `@[extern "lean_*"]` targets
-- via direct Rust ↔ Lean ABI calls (no intermediate C shim layer).
-- Adds `cargo` as a build prerequisite. Payoff: byte-for-byte
-- conformance with agave, version-pinned in
-- `qedsvm-rs/lean-bridge/Cargo.toml`. Builds as a member of the
-- `qedsvm-rs` Cargo workspace, so output lands at
-- `qedsvm-rs/target/release/libqedsvm_bridge.a`.
--
-- Scope (F1, reference semantics):
--   SVM.Pubkey     — Pubkey and Account data model
--   SVM.Solana.Cpi — invoke_signed envelope, well-known program IDs, discriminators
--   SVM.SBPF.*  — sBPF interpreter (ISA, Memory, Execute, WP tactic)
--
-- See README.md for scope.
package qedsvm

target rustBridge pkg : FilePath := do
  let manifestJob ← inputTextFile <| pkg.dir / "qedsvm-rs" / "lean-bridge" / "Cargo.toml"
  let libRsJob    ← inputTextFile <| pkg.dir / "qedsvm-rs" / "lean-bridge" / "src" / "lib.rs"
  let leanFfiJob  ← inputTextFile <| pkg.dir / "qedsvm-rs" / "lean-bridge" / "src" / "lean_ffi.rs"
  let manifest := pkg.dir / "qedsvm-rs" / "lean-bridge" / "Cargo.toml"
  let outFile  := pkg.dir / "qedsvm-rs" / "target" / "release" / "libqedsvm_bridge.a"
  manifestJob.bindM fun _ =>
    libRsJob.bindM fun _ =>
      leanFfiJob.mapM fun _ => do
        proc {
          cmd := "cargo"
          args := #["build", "--release", "--manifest-path", manifest.toString]
        }
        return outFile

extern_lib leanbridge pkg := do
  let archiveJob ← rustBridge.fetch
  let outFile := pkg.staticLibDir / nameToStaticLib "leanbridge"
  archiveJob.mapM fun srcLib => do
    IO.FS.createDirAll pkg.staticLibDir
    IO.FS.writeBinFile outFile (← IO.FS.readBinFile srcLib)
    return outFile

@[default_target]
lean_lib SVM where
  roots := #[`SVM]
  precompileModules := true

-- #40 gap 4: the per-call-site CPI envelope pair — the walk terminates at
-- the invoke (fail-closed proof-side CPI), the prefix post owns the
-- StableInstruction cells, and CpiEnvelopeDemo reshapes them into
-- `cpiEnvelope` (the envelope event, stated against the binary). Built in a
-- NON-precompiled lib: precompiling Generated.CpiEnvelopeCallerLifted yields
-- a module dylib whose load poisons downstream SL-statement elaboration
-- (segfault in the compiled path; the same proofs build and replay fine
-- interpreted — toolchain issue, not a proof issue).
lean_lib ExamplesCpi where
  srcDir := "examples/lean"
  roots := #[
    `Generated.CpiEnvelopeCallerLifted,
    `CpiEnvelopeDemo,
  ]

-- Examples — standalone proofs demonstrating the verification chain
-- on real hand-written sBPF programs. Not part of the core library;
-- build with `lake build Examples` to type-check the proofs.
lean_lib Examples where
  srcDir := "examples/lean"
  precompileModules := true
  roots := #[
    -- Soundness gate: fails the build if any flagship theorem acquires a
    -- non-standard axiom (sorry / native_decide / crypto). Keep first.
    `AxiomAudit,
    `SyscallHashPin,
    `H2Pin,
    `M4Pin,
    `M1Pin,
    `L1Pin,
    `ByteIncrement,
    `DischargePoC,
    `ProofDemo,
    `AsmTimeout,
    `MinimalTransferAsm,
    `CompilerRtFpCmp,
    `CompilerRtF64ToI64,
    `PToken.ValidationPrelude,
    `PToken.BalanceSpec,
    `PToken.RefinesTransfer,
    `PToken.TransferArm.L1Setup,
    `PToken.TransferArm.L2Bytecode,
    `PToken.TransferArm.L3TwoCalls,
    `PToken.TransferArm.L4TwoCallsExt,
    `PToken.TransferArm.L5ThirdCall,
    `PToken.TransferArm.L6FarJump,
    `PToken.TransferArm.H1Dispatch,
    `PToken.TransferArm.H3aAmountAlign,
    `PToken.TransferArm.H3bIndexBound,
    `PToken.TransferArm.H3cStateChecks,
    `PToken.TransferArm.H3dBalanceCheck,
    `PToken.TransferArm.H3dBalanceGuard,
    `PToken.TransferArm.H3eMintKeyCheck,
    `PToken.TransferArm.H3fSignerExit,
    `PToken.TransferArm.H4aDestMintCheck,
    `PToken.TransferArm.H4bBalanceMutation,
    `PToken.TransferArm.FullHappyPath,
    `PToken.TransferRefinement,
    `PToken.TransferCheckedRefinement,
    -- MintTo / Burn refinements: RESTORED 2026-06-12 on the
    -- regenerated (satisfiable-precondition) lifts — see the H8 note
    -- at the end of this list.
    `PToken.MintToRefinement,
    `PToken.BurnRefinement,
    `Multisig.MultisigGeneralization,
    -- Generated end-to-end lift demos (qedlift): .so → Lean module.
    -- Logger: a real, non-Pinocchio Solana program (Rust/solana-program)
    -- — generality proof that qedlift isn't p_token-specific. Crosses
    -- sol_log_ and a 64-bit multiply chain.
    `Generated.LoggerLifted,
    `Generated.ByteIncrementLifted,
    -- HeapAlloc: the embedded bump-allocator pattern over the program
    -- heap (reads/commits the bump slot at 0x300000000, writes + reads an
    -- allocated block). Proves a heap-allocating program lifts with the
    -- heap modeled as ordinary memory cells (no SL-core changes).
    -- The lift also carries a mechanically-emitted `HeapAlloc_allocates`
    -- corollary restating the heap cells via the `heapBumpPtr`/`heapBlock`
    -- SL predicates (a clean allocation claim).
    `Generated.HeapAllocLifted,
    -- HalfwordStore: all three halfword memory ops (ldxh / stxh / sth)
    -- in one straight line — the ST_H_IMM (sth_spec) pin on real
    -- cargo-build-sbf bytecode. Same fixture diff-tests vs mollusk.
    `Generated.HalfwordStoreLifted,
    -- Memcpy: the sol_memcpy_ happy path (call_sol_memcpy_spec) — two
    -- `↦Bytes` atoms (src readable, dst writable, disjoint), dst blob ← src,
    -- r0 := 0. The success-direction counterpart to oob_memset; wires the
    -- memory-op syscall family into the lift emitter.
    `Generated.MemcpyLifted,
    -- Memmove: the same shape via the `is_move` arm (call_sol_memmove_spec).
    `Generated.MemmoveLifted,
    -- Memcmp: two `↦Bytes` inputs + a `↦U32` output (call_sol_memcmp_spec),
    -- post value `memcmpResultU32`.
    `Generated.MemcmpLifted,
    -- SetReturnData: one `↦Bytes` input + the framed `↦ReturnData` atom
    -- (call_sol_set_return_data_spec), returnData ← input blob, r0 := 0.
    -- Wires the return-data syscall family into the lift emitter (Stage C).
    `Generated.SetReturnDataLifted,
    -- Single-slice sol_sha256 (call_sol_sha256_spec): program writes a
    -- one-entry SliceDesc, hashes the input slice into a 32-byte output
    -- (↦Bytes32 ← Sha256.hash inputBytes). Wires the hashing family (Stage D).
    `Generated.Sha256CallerLifted,
    -- Single-seed sol_create_program_address (call_sol_create_program_address_spec):
    -- derives a PDA from seed + program_id (↦Bytes32 ← Sha256.hash(seed ‖ pid ‖
    -- PDA_MARKER)); off-curve is a surfaced hypothesis. Wires the PDA family (Stage E).
    `Generated.PdaCreateLifted,
    -- AbortCaller: a happy path that ends in the `abort` syscall. Beyond the
    -- running-prefix `cuTripleWithinMem`, the lift emits a mechanized
    -- `AbortCaller_fault_correct` typed-fault corollary
    -- (`cuTripleFaultsWithinMem … .abort`), composing the prefix with
    -- `call_abort_faults_spec` via `cuTripleWithinMem_seq_fault_pure`. The
    -- emitter half of Phase 7 sub-item 3 (error corollaries via vmError) —
    -- surfaces `vmError = .abort` (audit L1's typed fault channel).
    `Generated.AbortCallerLifted,
    -- OobSecp256k1: a happy path that ends in an OUT-OF-BOUNDS `sol_secp256k1_recover`
    -- (r1 hash input points 256 MiB past the input region). The lift emits
    -- `OobSecp256k1_fault_correct : cuTripleFaultsWithinMem … .accessViolation`,
    -- composing the prefix with `call_sol_secp256k1_recover_faults_oob_spec`
    -- (frame_right-extended to the prefix post) via the Mem-Mem
    -- `cuTripleWithinMem_seq_fault` — combined rr = prefixRR ∧ OOB. The H6
    -- (accessViolation) arm of the Phase 7 sub-item 3 fault-corollary emitter.
    `Generated.OobSecp256k1Lifted,
    -- OobClockSysvar: an out-of-bounds `sol_get_clock_sysvar` (r1 output points
    -- past the writable region). Same OOB fault emitter as OobSecp256k1 but
    -- exercises the WRITE region guard (`rr` uses `containsWritable`, not
    -- `containsRange`) and a single-atom prefix post (the fault spec applies
    -- bare, no `frame_right`). Shows the OOB arm scales across syscall families.
    `Generated.OobClockSysvarLifted,
    -- OobRentSysvar: the H6 scale-out of the OOB fault emitter to the rent
    -- getter (17-byte execRent write region) — pure OobSyscall registration,
    -- no emitter changes.
    `Generated.OobRentSysvarLifted,
    -- OobSetReturnData: the register-sized-region OOB arm — the guarded
    -- slice is [r1, r1+r2), so the fault spec pins BOTH registers and the
    -- literal length side conditions discharge `by decide`.
    `Generated.OobSetReturnDataLifted,
    -- OobCreatePda: the non-r1-region OOB arm — the program_id slice
    -- [r3, r3+32) is the first guard, so the emitter rotates r3 to the
    -- front of the lifted pre/post before composing the fault spec.
    `Generated.OobCreatePdaLifted,
    -- OobSha256: the hash-family OOB arm — the digest output [r3, r3+32)
    -- is hashWrite's FIRST guard (non-r1 rotation on the WRITE side).
    `Generated.OobSha256Lifted,
    -- Counter: a real non-token .so re-lifted trace-style, plus the first
    -- NON-token asm-refines-intrinsic theorem (CounterRefinement →
    -- AsmRefinesCounterIncrement). Validates that the refinement codegen
    -- is layout-general, not SPL-token-shaped.
    `Generated.CounterTracedLifted,
    `Generated.CounterRefinement,
    -- Same counter.so, but the refinement is SPEC-DRIVEN: built from a
    -- qedspec-shaped `*.descriptor.json` (layout + mutated field + op),
    -- bypassing the hardcoded `refine_registry`. Targets the layout-general
    -- `AsmRefinesFieldUpdate` (not the bespoke `AsmRefinesCounterIncrement`).
    -- The prototype seam to qedspec — see docs/DEVEX_QEDSPEC_GAP.md.
    `Generated.CounterDescriptorTracedLifted,
    `Generated.CounterDescriptorRefinement,
    -- Same vault.so, but SPEC-DRIVEN from a descriptor (no refine_registry,
    -- no IDL). Exercises the layout-general multi-field framing (pubkey +
    -- byte) — the proof body is byte-identical to VaultRefinement above,
    -- confirming the descriptor path is layout-general, not counter-shaped.
    `Generated.VaultDescriptorTracedLifted,
    `Generated.VaultDescriptorRefinement,
    -- Same vault shape, descriptor-driven, but with a NON-1 constant delta
    -- (`total += 5`). Exercises the arbitrary-literal path: the lift cleans
    -- the +5 via `wrapAdd_const_of_lt` rather than the +1-specialized
    -- `wrapAdd_one_of_lt`. First descriptor refinement off the `+1` class.
    `Generated.VaultAdd5TracedLifted,
    `Generated.VaultAdd5Refinement,
    -- Same vault shape, but a PARAMETER delta (`total += amount`): the lift adds
    -- two memory reads (total + amount), cleaned by `wrapAdd_of_lt`, and the
    -- descriptor's `op.add_param` matches the second read as the credited amount.
    -- First descriptor refinement with a runtime (non-constant) delta.
    `Generated.VaultDepositTracedLifted,
    `Generated.VaultDepositRefinement,
    -- Vault: a multi-field NON-token account ({owner:Pubkey, total:u64,
    -- bump:u8}). The refinement (AsmRefinesFieldUpdate) reshapes the codec
    -- via the layout-general `account_agg` and frames the untouched
    -- owner+bump fields — mechanized multi-field non-token aggregation.
    `Generated.VaultTracedLifted,
    `Generated.VaultRefinement,
    -- Same vault.so, but the untouched `owner` field is described as a
    -- `[u8; 32]` blob in the IDL: exercises the blob/`account_agg` codegen
    -- path (`.blob [.gap g]` framed as `↦Bytes`, `memBytesIs_segs` reshape).
    `Generated.VaultBlobTracedLifted,
    `Generated.VaultBlobRefinement,
    -- A byte INSIDE the blob is lift-owned (read-only): the blob aggregation
    -- SPLITS into `[.gap, .byte, .gap]` (mechanized multisig-style split).
    `Generated.VaultSplitTracedLifted,
    `Generated.VaultSplitRefinement,
    `Generated.GuardedCounterLifted,
    -- #40 gap 1: per-path trace-guided lifts of guarded_counter (each
    -- carrying its mechanically-emitted `*_transition_path` corollary) +
    -- the emitted whole-transition bundle (success: counter credited,
    -- exit 0; abort: codec unchanged, exit 1).
    `Generated.GuardedCounterSuccessLifted,
    `Generated.GuardedCounterAbortLifted,
    `Generated.GuardedCounterTransition,
    -- The FAULT-path variant: guarded_abort's guard-fail path ends in the
    -- `abort` syscall, so its path corollary is `AsmRefinesTransitionFault`
    -- (typed .abort, codecs owned in the pre) and the bundle mixes
    -- obligation kinds.
    `Generated.GuardedAbortPanicLifted,
    `Generated.GuardedAbortSuccessLifted,
    `Generated.GuardedAbortTransition,
    -- The OOB-fault-path variant: guarded_oob's guard-fail path performs an
    -- out-of-bounds sol_get_clock_sysvar write, so its path corollary is an
    -- `AsmRefinesTransitionFault … .accessViolation` (combined rr = prefix
    -- ∧ OOB region condition).
    `Generated.GuardedOobOobLifted,
    `Generated.GuardedOobSuccessLifted,
    `Generated.GuardedOobTransition,
    `Generated.CounterWithHelperLifted,
    `Generated.TwoOpIncrementLifted,
    `Generated.TwoOpDecrementLifted,
    -- Trace-guided lifts: real p_token happy paths, balance/supply
    -- mutation in the post (qedlift --trace).
    `Generated.PTokenTransferTracedLifted,
    `Generated.PTokenTransferCheckedTracedLifted,
    -- MintTo + Burn: RESTORED via H8 Phase A+B (canonical cell
    -- aliasing resolves the r10 pointer-spill duplicate atoms; byte
    -- demotion of the width-mixed input-header reads is served by
    -- `ldxdw_bytes_spec` over per-byte atoms).
    `Generated.PTokenMintToTracedLifted,
    `Generated.PTokenBurnTracedLifted,
    -- CloseAccount: RESTORED via H8 Phase C-1 (the zeroing memset's
    -- pre-split specs expose the account dwords the program reads
    -- BEFORE the memset as `↦U64` cells, so the blob and the cells
    -- never overlap; `call_sol_memset_presplit_{,2}u64_spec`).
    `Generated.PTokenCloseAccountTracedLifted,
    -- InitializeMint2: RESTORED via H8 Phases B+C — crosses the
    -- faithful `sol_get_sysvar` (cells17 emission: the rent buffer as
    -- two `↦U64` cells + a byte with the concrete mollusk defaults),
    -- the stw tail-zeroing (byte-demoted, `stw_bytes_spec`), and a
    -- rent dword read spanning both (per-slot h_alias rewrites).
    -- Trace RE-CAPTURED under the H7-faithful VM (95 PCs vs the old
    -- zero-rent 199 — real values skip the soft-float zero path).
    `Generated.PTokenInitializeMint2TracedLifted
    -- H8 RETIREMENT/RESTORATION HISTORY (soundness audit, 2026-06-11/12).
    -- Four p_token traced lifts (+ the MintTo/Burn refinements) were
    -- found VACUOUS — qedlift's walker keyed cells by rendered address
    -- with no overlap analysis, so overlapping accesses emitted
    -- unsatisfiable sepConjs. All were retired, the walker gained a
    -- fail-closed overlap detector, and ALL are now RESTORED on
    -- satisfiable preconditions via the aliasing phases (canonical
    -- cell keys + h_alias equations; byte demotion with
    -- ldxdw_bytes/stw_bytes specs and per-slot address parameters;
    -- memset pre-split specs; the faithful sol_get_sysvar cells17
    -- emission). Every arm is pinned byte-for-byte against the
    -- emitter (qedlift inline tests). See
    -- docs/QEDLIFT_ALIASING_DESIGN.md.
  ]
