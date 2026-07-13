//! Reusable build-script helper for crates linking against the qedsvm Lean runtime.
//!
//! Cargo doesn't propagate `rustc-link-arg` across package boundaries, so downstream crates
//! that `use qedsvm` must call `emit_link_args` in their own `build.rs` or they get undefined
//! symbols like `_initialize_qedsvm_SVM_Ffi` at link time.
//!
//! Usage in `build.rs`:
//! ```ignore
//! fn main() {
//!     let root = std::env::var("QEDSVM_ROOT").unwrap_or_else(|_| "../qedsvm".to_string());
//!     qedsvm_buildscript::emit_link_args(std::path::Path::new(&root)).expect("qedsvm link args");
//! }
//! ```
//! `[build-dependencies] qedsvm-buildscript = { path = "../qedsvm/qedsvm-rs/qedsvm-buildscript" }`

use std::path::{Path, PathBuf};
use std::process::Command;

/// Configuration/environment errors from `emit_link_args`.
#[derive(Debug)]
pub enum Error {
    /// `lean --print-prefix` couldn't run (toolchain not on PATH).
    LeanToolchainNotFound,
    /// `lean --print-prefix` returned non-zero or non-UTF-8.
    LeanPrefixUnreadable,
    /// `.lake/build/lib/lean/` missing — run `lake build` first.
    LakeArtifactsMissing(PathBuf),
    /// Zero `qedsvm_*.dylib` found — partial Lake build?
    NoQedsvmDylibs(PathBuf),
    /// `libleanbridge.a` missing — run `lake build` first.
    LeanBridgeArchiveMissing(PathBuf),
    /// Lean runtime dylib missing from toolchain prefix — toolchain layout changed?
    LeanRuntimeDylibMissing(PathBuf),
    BridgeSourceUnreadable(PathBuf, std::io::Error),
    /// Zero `pub extern "C" fn lean_*` found — refusing to link (would SIGSEGV on first crypto call).
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
                write!(
                    f,
                    "`lean --print-prefix` returned a non-zero status or invalid output"
                )
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

/// Emit `cargo:rustc-link-*` directives for linking against the qedsvm Lean runtime.
///
/// Walks `.lake/build/lib/lean/` under `qedsvm_root`, links all `qedsvm_*.dylib` modules,
/// force-loads `lean_*` exports from `libleanbridge.a` via `-Wl,-u`, and emits
/// `rerun-if-changed` triggers for the bridge source + `SVM/Ffi.lean`.
pub fn emit_link_args(qedsvm_root: &Path) -> Result<(), Error> {
    let prefix = lean_prefix()?;
    let lean_include = prefix.join("include");
    let lean_lib_dir = prefix.join("lib").join("lean");
    let lean_lib_root = prefix.join("lib");
    // Advertise include dir for downstream cc::Build needing lean/lean.h.
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

    for d in [&lean_lib_dir, &lean_lib_root, &lake_lean_dir, &lake_lib_dir] {
        println!("cargo:rustc-link-search=native={}", d.display());
    }
    for d in [&lean_lib_dir, &lean_lib_root, &lake_lean_dir, &lake_lib_dir] {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", d.display());
    }

    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!("cargo:rustc-link-lib=dylib=Lake_shared");

    // Pass qedsvm_*.dylib positionally (not via -l) because Lake filenames lack the `lib` prefix.
    // Linux --as-needed would drop modules only referenced by other modules' initialize_* symbols
    // at load time — defeat it with --no-as-needed for just these dylibs.
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-Wl,--no-as-needed");
    }
    let mut count = 0;
    for entry in std::fs::read_dir(&lake_lean_dir)
        .map_err(|_| Error::LakeArtifactsMissing(lake_lean_dir.clone()))?
    {
        let Ok(entry) = entry else { continue };
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|s| s.to_str()) else {
            continue;
        };
        let is_dyn = name.ends_with(".dylib") || name.ends_with(".so");
        if !is_dyn || !name.starts_with("qedsvm_") {
            continue;
        }
        println!("cargo:rustc-link-arg={}", path.display());
        // Relink on dylib change so cargo test never runs stale Lean semantics (M14 stale-link half).
        println!("cargo:rerun-if-changed={}", path.display());
        count += 1;
    }
    if count == 0 {
        return Err(Error::NoQedsvmDylibs(lake_lean_dir));
    }
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-Wl,--as-needed");
    }

    // Force-load lean_* exports from libleanbridge.a so Lean dylibs' dynamic-lookup refs resolve.
    // Symbol list is scraped from lib.rs — adding a new export there propagates here automatically.
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

    // libleanbridge.a must come AFTER -u flags (macOS ld is single-pass; -u only pulls from later archives).
    let leanbridge_a = lake_lib_dir.join("libleanbridge.a");
    if !leanbridge_a.exists() {
        return Err(Error::LeanBridgeArchiveMissing(leanbridge_a));
    }
    println!("cargo:rustc-link-arg={}", leanbridge_a.display());
    println!("cargo:rerun-if-changed={}", leanbridge_a.display());

    // Pass libleanshared + libLake_shared positionally so cargo can't strip them as "unreferenced".
    // Extension is .dylib on macOS, .so on Linux.
    let dylib_ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let leanshared = lean_lib_dir.join(format!("libleanshared.{dylib_ext}"));
    let lake_shared = lean_lib_dir.join(format!("libLake_shared.{dylib_ext}"));
    for p in [&leanshared, &lake_shared] {
        if !p.exists() {
            return Err(Error::LeanRuntimeDylibMissing(p.clone()));
        }
        println!("cargo:rustc-link-arg={}", p.display());
    }

    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-rdynamic");
        // libleanbridge.a is a Rust staticlib — bundles its own std/core. Linux rust-lld treats
        // duplicate symbols as errors; allow first-wins (symbols are byte-identical same-toolchain).
        println!("cargo:rustc-link-arg=-Wl,--allow-multiple-definition");
    }
    if cfg!(target_os = "macos") {
        println!("cargo:rustc-link-arg=-Wl,-export_dynamic");
    }

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

/// Scrape `pub extern "C" fn lean_*` names from a Rust source file for the `-Wl,-u` list.
fn parse_lean_exports(path: &Path) -> Result<Vec<String>, Error> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| Error::BridgeSourceUnreadable(path.to_path_buf(), e))?;
    let needle = "pub extern \"C\" fn lean_";
    let mut out = Vec::new();
    for line in src.lines() {
        let line = line.trim_start();
        let Some(rest) = line.strip_prefix(needle) else {
            continue;
        };
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
