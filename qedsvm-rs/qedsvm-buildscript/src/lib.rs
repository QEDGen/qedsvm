//! Reusable build-script helper for crates linking against the
//! qedsvm Lean runtime.
//!
//! Background: `qedsvm-rs/build.rs` emits ~80 `cargo:rustc-link-arg`
//! directives that wire up:
//!   - Lean's runtime (`libleanshared`, `libLake_shared`)
//!   - Every `qedsvm_*.dylib` Lake produced
//!   - Force-load symbols from `libleanbridge.a` (via `-Wl,-u`)
//!   - macOS `-export_dynamic` / Linux `-rdynamic` so dyld can
//!     resolve the Lean dylibs' `-undefined,dynamic_lookup` refs
//!     at runtime
//!
//! Cargo doesn't propagate `rustc-link-arg` from a dependency's
//! `build.rs` to dependent crates' final link command — it only
//! applies them within the same package. So a downstream crate
//! depending on `qedsvm` as a library link-fails with undefined
//! symbols like `_initialize_qedsvm_SVM_Ffi` unless it replicates
//! the entire Lake/Lean discovery + link-arg setup in its own
//! `build.rs`.
//!
//! This crate centralises that setup. Downstream usage:
//!
//! ```ignore
//! // In your build.rs:
//! fn main() {
//!     let qedsvm_root = std::env::var("QEDSVM_ROOT")
//!         .unwrap_or_else(|_| "../qedsvm".to_string());
//!     qedsvm_buildscript::emit_link_args(
//!         std::path::Path::new(&qedsvm_root),
//!     )
//!     .expect("emit qedsvm link args");
//! }
//! ```
//!
//! And in your `Cargo.toml`:
//!
//! ```toml
//! [build-dependencies]
//! qedsvm-buildscript = { path = "../qedsvm/qedsvm-rs/qedsvm-buildscript" }
//! ```
//!
//! When the qedsvm `build.rs` evolves (new dylibs, new Lake layout,
//! changed force-load list), downstream crates pick up the change
//! by re-running cargo — no manual sync.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Errors `emit_link_args` can surface. All are configuration /
/// environment issues at the build-script level.
#[derive(Debug)]
pub enum Error {
    /// `lean --print-prefix` couldn't run (toolchain not on PATH).
    LeanToolchainNotFound,
    /// `lean --print-prefix` ran but returned non-zero or non-UTF-8.
    LeanPrefixUnreadable,
    /// `.lake/build/lib/lean/` doesn't exist under `qedsvm_root` —
    /// caller must `lake build` in the qedsvm checkout first.
    LakeArtifactsMissing(PathBuf),
    /// We walked `.lake/build/lib/lean/` and found zero
    /// `qedsvm_*.dylib` (or `.so`) files. Most likely cause: a
    /// partial Lake build.
    NoQedsvmDylibs(PathBuf),
    /// `libleanbridge.a` is missing from `.lake/build/lib/`. Same
    /// remedy: `lake build` in the qedsvm checkout.
    LeanBridgeArchiveMissing(PathBuf),
    /// A required Lean runtime dylib is missing from the toolchain
    /// prefix. Almost always a sign the toolchain layout changed
    /// across a Lean version we haven't validated.
    LeanRuntimeDylibMissing(PathBuf),
    /// The bridge source file isn't readable. Carries the IO
    /// error for diagnosis.
    BridgeSourceUnreadable(PathBuf, std::io::Error),
    /// Bridge source exists but exports zero `pub extern "C" fn
    /// lean_*` symbols. Linking would silently produce a binary
    /// that SIGSEGVs the first time the Lean side calls a crypto
    /// syscall — refuse instead.
    NoLeanBridgeExports(PathBuf),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LeanToolchainNotFound => write!(
                f,
                "`lean --print-prefix` failed — is the Lean toolchain on PATH?",
            ),
            Self::LeanPrefixUnreadable => {
                write!(f, "`lean --print-prefix` returned a non-zero status or invalid output")
            }
            Self::LakeArtifactsMissing(p) => write!(
                f,
                "Lake build output missing at {}.\n\
                 Run `lake build` in the qedsvm checkout first.",
                p.display(),
            ),
            Self::NoQedsvmDylibs(p) => write!(
                f,
                "Found 0 qedsvm_*.dylib in {} — did `lake build` complete?",
                p.display(),
            ),
            Self::LeanBridgeArchiveMissing(p) => write!(
                f,
                "Missing {} — did `lake build` produce the static archive?",
                p.display(),
            ),
            Self::LeanRuntimeDylibMissing(p) => write!(
                f,
                "Missing {} — Lean toolchain layout changed?",
                p.display(),
            ),
            Self::BridgeSourceUnreadable(p, e) => {
                write!(f, "read {}: {e}", p.display())
            }
            Self::NoLeanBridgeExports(p) => write!(
                f,
                "Found 0 `pub extern \"C\" fn lean_*` exports in {} — \
                 refusing to link without any crypto FFI symbols.",
                p.display(),
            ),
        }
    }
}

impl std::error::Error for Error {}

/// Emit the `cargo:rustc-link-*` directives needed to link a
/// downstream crate against the qedsvm Lean runtime.
///
/// `qedsvm_root` is the qedsvm checkout directory — the one
/// containing `lakefile.lean` and a built `.lake/`. The function
/// looks for `.lake/build/lib/lean/` underneath, finds all
/// `qedsvm_*.dylib` (or `.so`) modules Lake produced, and emits
/// link-args for each. It also force-loads the crypto-bridge
/// archive's `lean_*` exports via `-Wl,-u`.
///
/// Re-run triggers (`cargo:rerun-if-changed`) are emitted for
/// the bridge source and the workspace `Ffi.lean` entrypoint so
/// a Lean-side change rebuilds the downstream binary.
pub fn emit_link_args(qedsvm_root: &Path) -> Result<(), Error> {
    let prefix = lean_prefix()?;
    let lean_include = prefix.join("include");
    let lean_lib_dir = prefix.join("lib").join("lean");
    let lean_lib_root = prefix.join("lib");
    // `lean_include` is exposed for downstream `cc::Build`s that
    // need `lean/lean.h`; we don't use it here, but advertising it
    // via `cargo:include` (cargo's de-facto channel for include
    // dirs) is the conventional way to pass it on.
    println!("cargo:include={}", lean_include.display());

    let lake_lean_dir = qedsvm_root
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean");
    let lake_lib_dir = qedsvm_root.join(".lake").join("build").join("lib");

    if !lake_lean_dir.exists() {
        return Err(Error::LakeArtifactsMissing(lake_lean_dir));
    }

    // Search paths.
    for d in [&lean_lib_dir, &lean_lib_root, &lake_lean_dir, &lake_lib_dir] {
        println!("cargo:rustc-link-search=native={}", d.display());
    }
    // rpath for runtime loader.
    for d in [&lean_lib_dir, &lean_lib_root, &lake_lean_dir, &lake_lib_dir] {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", d.display());
    }

    // Lean runtime + Lake's shared lib.
    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!("cargo:rustc-link-lib=dylib=Lake_shared");

    // Every qedsvm_*.dylib Lake produced. We pass these as
    // positional link-args (not `-l` flags) because Lake's filenames
    // (`qedsvm_SVM_Ffi.dylib`) lack the `lib` prefix that
    // `rustc-link-lib=dylib=NAME` expects.
    // On Linux, rustc passes `-Wl,--as-needed`, which drops any of these
    // module `.so`s the binary doesn't reference *directly* from its
    // DT_NEEDED list. But the modules reference each other's
    // `initialize_*` symbols at load time (e.g. `Ffi.so` needs
    // `initialize_qedsvm_SVM_SBPF_Runner`), so a dropped module is missing
    // at runtime → "undefined symbol" on startup. Keep them all needed.
    // (macOS doesn't use --as-needed, so no-op there.)
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-Wl,--no-as-needed");
    }
    let mut count = 0;
    for entry in std::fs::read_dir(&lake_lean_dir)
        .map_err(|_| Error::LakeArtifactsMissing(lake_lean_dir.clone()))?
    {
        let Ok(entry) = entry else { continue };
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|s| s.to_str()) else { continue };
        let is_dyn = name.ends_with(".dylib") || name.ends_with(".so");
        if !is_dyn || !name.starts_with("qedsvm_") {
            continue;
        }
        println!("cargo:rustc-link-arg={}", path.display());
        count += 1;
    }
    if count == 0 {
        return Err(Error::NoQedsvmDylibs(lake_lean_dir));
    }
    // Restore the default for the remaining libs (which ARE referenced).
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-Wl,--as-needed");
    }

    // Force-load every `lean_*` export from libleanbridge.a so the
    // Lean dylibs' undefined-dynamic-lookup refs resolve at runtime.
    // We derive the symbol list by parsing `lean-bridge/src/lib.rs`
    // for `pub extern "C" fn lean_*` decls — adding a new syscall
    // export there propagates here automatically.
    let bridge_src = qedsvm_root
        .join("qedsvm-rs")
        .join("lean-bridge")
        .join("src")
        .join("lib.rs");
    let ffi_syms = parse_lean_exports(&bridge_src)?;
    if ffi_syms.is_empty() {
        return Err(Error::NoLeanBridgeExports(bridge_src));
    }
    let undersym_prefix = if cfg!(target_os = "macos") { "_" } else { "" };
    for sym in &ffi_syms {
        println!("cargo:rustc-link-arg=-Wl,-u,{}{}", undersym_prefix, sym);
    }

    // libleanbridge.a must come AFTER the -u flags on the link cmd
    // (macOS `ld` is single-pass; `-u` only pulls a symbol from an
    // archive that appears later). Pass it positionally rather than
    // via `link-lib=static=...` to control ordering.
    let leanbridge_a = lake_lib_dir.join("libleanbridge.a");
    if !leanbridge_a.exists() {
        return Err(Error::LeanBridgeArchiveMissing(leanbridge_a));
    }
    println!("cargo:rustc-link-arg={}", leanbridge_a.display());

    // libleanbridge.a's objects reference Lean runtime symbols in
    // libleanshared / libLake_shared. cargo strips
    // `link-lib=dylib=*` entries it thinks are unreferenced, so the
    // dylibs disappear from the final cc invocation. Pass them
    // positionally too so they participate in symbol resolution.
    // Runtime shared-library extension is platform-specific: `.dylib`
    // on macOS, `.so` on Linux (CI). (The `qedsvm_*` module loop above
    // already accepts either extension.)
    let dylib_ext = if cfg!(target_os = "macos") { "dylib" } else { "so" };
    let leanshared = lean_lib_dir.join(format!("libleanshared.{dylib_ext}"));
    let lake_shared = lean_lib_dir.join(format!("libLake_shared.{dylib_ext}"));
    for p in [&leanshared, &lake_shared] {
        if !p.exists() {
            return Err(Error::LeanRuntimeDylibMissing(p.clone()));
        }
        println!("cargo:rustc-link-arg={}", p.display());
    }

    // Export the binary's dynamic symbol table.
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-rdynamic");
        // `libleanbridge.a` is a Rust `staticlib`, so it bundles its own
        // copy of `std`/`core` (assert_failed, fmt builders, …). The main
        // binary links `core` too, so the two collide. macOS's `ld`
        // tolerates duplicate symbols (first definition wins); Linux's
        // `rust-lld` treats them as errors. Allow first-wins to match —
        // the symbols are byte-identical (same rustc/toolchain).
        println!("cargo:rustc-link-arg=-Wl,--allow-multiple-definition");
    }
    if cfg!(target_os = "macos") {
        println!("cargo:rustc-link-arg=-Wl,-export_dynamic");
    }

    // Re-run triggers.
    println!("cargo:rerun-if-changed={}", bridge_src.display());
    let ffi_lean = qedsvm_root.join("SVM").join("Ffi.lean");
    println!("cargo:rerun-if-changed={}", ffi_lean.display());

    Ok(())
}

fn lean_prefix() -> Result<PathBuf, Error> {
    let out = Command::new("lean")
        .args(["--print-prefix"])
        .output()
        .map_err(|_| Error::LeanToolchainNotFound)?;
    if !out.status.success() {
        return Err(Error::LeanPrefixUnreadable);
    }
    let s = String::from_utf8(out.stdout).map_err(|_| Error::LeanPrefixUnreadable)?;
    Ok(PathBuf::from(s.trim()))
}

/// Scrape `pub extern "C" fn lean_<name>(` declarations out of a Rust
/// source file. Used to derive the `-Wl,-u` list from the bridge's
/// actual exports rather than maintaining a parallel const here.
fn parse_lean_exports(path: &Path) -> Result<Vec<String>, Error> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| Error::BridgeSourceUnreadable(path.to_path_buf(), e))?;
    let needle = "pub extern \"C\" fn lean_";
    let mut out = Vec::new();
    for line in src.lines() {
        let line = line.trim_start();
        let Some(rest) = line.strip_prefix(needle) else { continue };
        let name_tail: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if !name_tail.is_empty() {
            out.push(format!("lean_{name_tail}"));
        }
    }
    Ok(out)
}
