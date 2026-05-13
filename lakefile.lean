import Lake
open Lake DSL System

-- formal-svm — Lean 4 reference semantics for the Solana Virtual Machine.
--
-- Pure Lean 4, no Mathlib dependency. Anything that needs Mathlib-level
-- reasoning (`Fin → α`, `BigOperators`, ring/omega over closed forms)
-- belongs in a downstream consumer, not here.
--
-- C FFI: the `csrc/` directory holds vendored reference implementations
-- of cryptographic syscalls (Keccak-256, Blake3, secp256k1_recover, ...)
-- that we wire up via `@[extern]`. Pure-Lean replacements can come later
-- per syscall; FFI is the path-of-least-resistance so the runner can
-- execute real programs without each crypto primitive being its own
-- pre-requisite project.
--
-- Scope (F1, reference semantics):
--   Svm.Account — Pubkey and Account data model
--   Svm.Cpi     — invoke_signed envelope, well-known program IDs, discriminators
--   Svm.SBPF.*  — sBPF interpreter (ISA, Memory, Execute, WP tactic)
--
-- See README.md and ROADMAP.md for scope.
package formalSvm

target keccak256.o pkg : FilePath := do
  let oFile := pkg.buildDir / "csrc" / "keccak256.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "keccak256.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall"] "cc"

extern_lib leankeccak pkg := do
  let name := nameToStaticLib "leankeccak"
  let oJob ← keccak256.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

target blake3.o pkg : FilePath := do
  let oFile := pkg.buildDir / "csrc" / "blake3.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "blake3.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall"] "cc"

extern_lib leanblake3 pkg := do
  let name := nameToStaticLib "leanblake3"
  let oJob ← blake3.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

-- secp256k1 ECDSA recovery, curve25519, and (eventually) other Solana
-- crypto syscalls go through `rust-bridge/`, a tiny `cargo` staticlib
-- that pulls the exact crates agave uses on master (`libsecp256k1`
-- 0.7.2 paritytech, `curve25519-dalek` 4.1.3, etc.) and exposes them
-- via a C ABI. The C wrappers in `csrc/` translate between Lean's
-- `lean_object` representation and the bridge's raw-pointer ABI.
--
-- Cost: this adds `cargo` as a build prerequisite. Payoff: byte-for-
-- byte conformance with agave's runtime, including edge cases like
-- high-S signature rejection.
target rustBridge pkg : FilePath := do
  let manifestJob ← inputTextFile <| pkg.dir / "rust-bridge" / "Cargo.toml"
  let libRsJob    ← inputTextFile <| pkg.dir / "rust-bridge" / "src" / "lib.rs"
  let manifest := pkg.dir / "rust-bridge" / "Cargo.toml"
  let outFile  := pkg.dir / "rust-bridge" / "target" / "release" / "libformal_svm_bridge.a"
  manifestJob.bindM fun _ =>
    libRsJob.mapM fun _ => do
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

target secp256k1_recover.o pkg : FilePath := do
  let oFile := pkg.buildDir / "csrc" / "secp256k1_recover.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "secp256k1_recover.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall"] "cc"

extern_lib leansecp256k1 pkg := do
  let name := nameToStaticLib "leansecp256k1"
  let oJob ← secp256k1_recover.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

-- Audit shim: exposes the agave-pinned `sha2` / `sha3` / `blake3`
-- Rust crates to Lean for byte-equivalence testing against the
-- production hash paths (`Sha256.hash`, `Keccak256.hash`,
-- `Blake3.hash`). See Demo 28 in `RunnerDemo.lean`.
target hash_bridge.o pkg : FilePath := do
  let oFile := pkg.buildDir / "csrc" / "hash_bridge.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "hash_bridge.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-Wall"] "cc"

extern_lib leanhashbridge pkg := do
  let name := nameToStaticLib "leanhashbridge"
  let oJob ← hash_bridge.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

@[default_target]
lean_lib Svm where
  roots := #[`Svm]
  precompileModules := true
