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
  roots := #[
    `ByteIncrement,
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
    `PToken.MirRefines,
    `PToken.TransferAggregation,
    `PToken.TransferRefinement,
    `PToken.TransferCheckedRefinement,
    `PToken.MintAggregation,
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
    `Generated.GuardedCounterLifted,
    `Generated.CounterWithHelperLifted,
    `Generated.TwoOpIncrementLifted,
    `Generated.TwoOpDecrementLifted,
    -- Trace-guided lifts: real p_token happy paths, balance/supply
    -- mutation in the post (qedlift --trace). MintTo also demonstrates
    -- that trace guidance sidesteps the static walker's phantom loop.
    `Generated.PTokenTransferTracedLifted,
    `Generated.PTokenMintToTracedLifted,
    `Generated.PTokenBurnTracedLifted,
    `Generated.PTokenTransferCheckedTracedLifted,
    -- CloseAccount: first arm whose happy path crosses a host syscall
    -- (`sol_memset_` zeroing the account data). qedlift threads it via
    -- `call_sol_memset_spec` (a `↦Bytes` blob + surfaced CU/size hyps).
    `Generated.PTokenCloseAccountTracedLifted,
    -- InitializeMint2: crosses sol_get_sysvar + 7 nested call_locals +
    -- spilled registers + the densest ALU/jump mix. First lift to
    -- exercise the full call_local machinery; builds after the
    -- sl_block_iter discharge perf fix (O(n²) → O(n)).
    `Generated.PTokenInitializeMint2TracedLifted
  ]
  -- NOTE: no `precompileModules` here (unlike the core `SVM` lib). On the
  -- pinned toolchain (v4.30.0-rc2), the precompiled native dylib for the
  -- aggregation modules (e.g. `PToken.MintAggregation`) type-checks but
  -- *segfaults on dlopen*, which crashed every downstream importer (the
  -- four asm-refines-intrinsic modules) at import time — not in the proof,
  -- which is why a stubbed `sorry` body still crashed. Precompilation only
  -- speeds native_decide/#eval; the kernel still fully checks every proof
  -- without it, so dropping it here is sound and costs ~nothing (Examples
  -- builds in ~40s). Revisit once the toolchain is bumped.
