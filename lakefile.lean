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
-- See README.md and ROADMAP.md for scope.
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
    `PToken.TransferArm.H3eMintKeyCheck,
    `PToken.TransferArm.H3fSignerExit,
    `PToken.TransferArm.H4aDestMintCheck,
    `PToken.TransferArm.H4bBalanceMutation,
    `PToken.TransferArm.FullHappyPath,
    `PToken.TransferAggregation,
    `PToken.TransferRefinement,
    `PToken.TransferCheckedRefinement,
    `PToken.MintAggregation,
    -- MintToRefinement / BurnRefinement are RETIRED with their lifts —
    -- see the retirement note at the end of this list.
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
    -- Counter: a real non-token .so re-lifted trace-style, plus the first
    -- NON-token asm-refines-intrinsic theorem (CounterRefinement →
    -- AsmRefinesCounterIncrement). Validates that the refinement codegen
    -- is layout-general, not SPL-token-shaped.
    `Generated.CounterTracedLifted,
    `Generated.CounterRefinement,
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
    `Generated.GuardedCounterLifted,
    `Generated.CounterWithHelperLifted,
    `Generated.TwoOpIncrementLifted,
    `Generated.TwoOpDecrementLifted,
    -- Trace-guided lifts: real p_token happy paths, balance/supply
    -- mutation in the post (qedlift --trace).
    `Generated.PTokenTransferTracedLifted,
    `Generated.PTokenTransferCheckedTracedLifted
    -- RETIREMENT NOTE (soundness audit H7/H8, 2026-06-11/12). Four
    -- p_token traced lifts and the two refinements built on them are
    -- retired pending regeneration, because qedlift's walker keyed
    -- memory cells by RENDERED address with no overlap analysis: two
    -- accesses to overlapping bytes through different renderings
    -- emitted two overlapping atoms, making the precondition's
    -- sepConj UNSATISFIABLE — the theorems were VACUOUSLY true.
    -- qedlift now detects footprint overlap on a canonical
    -- (root, displacement) form and fails closed. The casualties,
    -- each confirmed by re-running the emitter on its .pcs trace:
    --   * PTokenMintToTracedLifted + PToken.MintToRefinement —
    --     duplicate cells: pinocchio spills pointers via r10
    --     ([r10-2064], [r10-2056]) and reloads them through a struct
    --     base (addr1 = r10-2072, offsets +8/+16).
    --   * PTokenBurnTracedLifted + PToken.BurnRefinement — same
    --     duplicate-cell pattern.
    --   * PTokenCloseAccountTracedLifted — a load at baseAddr+88
    --     INSIDE the sol_memset blob [baseAddr+48, +96) (also note:
    --     the fresh-variable read should have been the memset fill).
    --   * PTokenInitializeMint2TracedLifted — overlapping `↦U32`
    --     tail-zeroing stores (`stw [r10-4]; stw [r10-7]`); ALSO
    --     traced against the pre-H7 zero-filling `sol_get_sysvar`.
    -- Transfer / TransferChecked re-emit byte-identical under the
    -- detector and remain (with their refinements) — the flagship
    -- balance theorems are NOT affected. Restoration = walker
    -- aliasing (canonical cell keys + h_alias address equations for
    -- duplicates; byte-granular demotion for partial overlap; blob
    -- read-through for memset/get_sysvar regions), tracked under H8 —
    -- see docs/QEDLIFT_ALIASING_DESIGN.md. Runtime diff coverage of
    -- all four arms is unaffected (p_token_* diff tests).
  ]
