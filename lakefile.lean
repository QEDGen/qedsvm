import Lake
open Lake DSL System

-- formal-svm — Lean 4 reference semantics for the Solana Virtual Machine.
--
-- Pure Lean 4, no Mathlib dependency. Anything that needs Mathlib-level
-- reasoning (`Fin → α`, `BigOperators`, ring/omega over closed forms)
-- belongs in a downstream consumer, not here.
--
-- Native crypto: every cryptographic syscall goes through `rust-bridge/`,
-- a `cargo` staticlib that pulls the exact crates agave's runtime uses
-- (`libsecp256k1 = 0.7.2` paritytech, `curve25519-dalek = 4.1.3`,
-- `sha2 = 0.10.8`, `sha3 = 0.10.8`, `blake3 = 1.8.5`) and exposes them
-- as `@[extern "lean_*"]` targets via direct Rust ↔ Lean ABI calls (no
-- intermediate C shim layer). Adds `cargo` as a build prerequisite.
-- Payoff: byte-for-byte conformance with agave, version-pinned in
-- `rust-bridge/Cargo.toml`.
--
-- Scope (F1, reference semantics):
--   Svm.Account — Pubkey and Account data model
--   Svm.Cpi     — invoke_signed envelope, well-known program IDs, discriminators
--   Svm.SBPF.*  — sBPF interpreter (ISA, Memory, Execute, WP tactic)
--
-- See README.md and ROADMAP.md for scope.
package formalSvm

target rustBridge pkg : FilePath := do
  let manifestJob ← inputTextFile <| pkg.dir / "rust-bridge" / "Cargo.toml"
  let libRsJob    ← inputTextFile <| pkg.dir / "rust-bridge" / "src" / "lib.rs"
  let leanFfiJob  ← inputTextFile <| pkg.dir / "rust-bridge" / "src" / "lean_ffi.rs"
  let manifest := pkg.dir / "rust-bridge" / "Cargo.toml"
  let outFile  := pkg.dir / "rust-bridge" / "target" / "release" / "libformal_svm_bridge.a"
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
lean_lib Svm where
  roots := #[`Svm]
  precompileModules := true
