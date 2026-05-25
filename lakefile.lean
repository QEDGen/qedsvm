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
    `PToken.TransferArm.H3fSignerExit
  ]
  precompileModules := true
