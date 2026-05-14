//! Discover Lean's runtime + Lake's build output and wire them into
//! the linker.
//!
//! formal-svm uses `precompileModules := true`, so each Lean module
//! is its own `.dylib` (~30 in total). Rather than hardcode the list
//! (which drifts as the codebase evolves), we enumerate the
//! `.lake/build/lib/lean/` directory and link every `formalSvm_*`
//! dylib we find. Lean's `-undefined,dynamic_lookup` link mode means
//! cross-module symbols resolve at runtime — we just need every
//! transitive dep loaded into the process.
//!
//! Prerequisite: the user has run `lake build` in the workspace root.
//! We re-trigger when our Lean entrypoint changes; we don't drive
//! `lake build` from here because cargo-from-lake is the supported
//! direction (see workspace `lakefile.lean`) and reversing it would
//! produce a circular build.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    // ─ Lean prefix (libleanshared + libLake_shared live here). ────
    let prefix = run_capture("lean", &["--print-prefix"])
        .expect("`lean --print-prefix` failed — is the Lean toolchain on PATH?");
    let prefix = prefix.trim();
    let lean_include = PathBuf::from(prefix).join("include");
    let lean_lib_dir = PathBuf::from(prefix).join("lib").join("lean");
    let lean_lib_root = PathBuf::from(prefix).join("lib");

    // ─ Build our own glue C file (init/teardown wrappers). ────────
    cc::Build::new()
        .file("csrc/init_glue.c")
        .include(&lean_include)
        .opt_level(2)
        .warnings(true)
        .compile("formalsvmglue");
    println!("cargo:rerun-if-changed=csrc/init_glue.c");

    // ─ Lake build output (one dylib per Lean module). ─────────────
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("CARGO_MANIFEST_DIR has a parent")
        .to_path_buf();
    let lake_lean_dir = workspace_root
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean");
    let lake_lib_dir = workspace_root.join(".lake").join("build").join("lib");

    if !lake_lean_dir.exists() {
        panic!(
            "Lake build output missing at {}.\n\
             Run `lake build` in the workspace root before building formal-svm-rs.",
            lake_lean_dir.display()
        );
    }

    // ─ Search paths. ──────────────────────────────────────────────
    for d in [&lean_lib_dir, &lean_lib_root, &lake_lean_dir, &lake_lib_dir] {
        println!("cargo:rustc-link-search=native={}", d.display());
    }

    // ─ rpath so the runtime loader finds the dylibs (macOS + Linux).
    for d in [&lean_lib_dir, &lean_lib_root, &lake_lean_dir, &lake_lib_dir] {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", d.display());
    }

    // ─ Lean runtime + Lake's shared lib (init chases through it). ─
    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!("cargo:rustc-link-lib=dylib=Lake_shared");

    // ─ Every formalSvm module dylib produced by Lake. ─────────────
    //
    // Lake emits them with the module-mangled name and no `lib`
    // prefix (e.g. `formalSvm_Svm_Ffi.dylib`), so cargo's normal
    // `rustc-link-lib=dylib=NAME` (which expects `libNAME.dylib`)
    // doesn't find them. Pass the absolute path via
    // `rustc-link-arg` instead — clang/ld accept a `.dylib` path as
    // a positional arg and link it directly.
    let mut count = 0;
    for entry in std::fs::read_dir(&lake_lean_dir).expect("read lake lib dir") {
        let entry = entry.expect("read dir entry");
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|s| s.to_str()) else { continue };
        let is_dyn = name.ends_with(".dylib") || name.ends_with(".so");
        if !is_dyn || !name.starts_with("formalSvm_") { continue }
        println!("cargo:rustc-link-arg={}", path.display());
        count += 1;
    }
    if count == 0 {
        panic!(
            "Found 0 formalSvm_*.dylib in {} — did `lake build` complete?",
            lake_lean_dir.display()
        );
    }

    // ─ The Rust-bridge staticlib (resolves crypto syscalls). ──────
    //
    // The Lean dylibs (`formalSvm_Svm_SBPF_Curve25519.dylib`, etc.)
    // are linked with `-undefined,dynamic_lookup` and have undefined
    // refs like `_lean_curve_validate_edwards` that dyld is supposed
    // to resolve at runtime by searching all loaded images.
    //
    // A plain `link-lib=static=leanbridge` is NOT enough: the
    // linker only pulls archive objects whose symbols are referenced
    // by THIS binary's own code. Since the test binary never
    // references `lean_curve_*` from Rust, those symbols are absent
    // from the image's exports; dyld searches at runtime and finds
    // nothing, and the lazy stub branches to 0 → SIGSEGV inside
    // Curve25519.execValidate.
    //
    // Force-loading the whole archive (`-Wl,-force_load,...`) pulls
    // in 200+ duplicate Rust std/core symbols because rust-bridge
    // statically embeds them. Instead we tell the linker each FFI
    // symbol we want is "needed" via `-Wl,-u,<sym>` — this pulls
    // *only* the object containing that symbol from the archive,
    // leaving the rest (and the std/core duplicates) alone.
    //
    // The list mirrors `pub extern "C" fn lean_*` in
    // `rust-bridge/src/lib.rs`. When you add a new FFI export
    // there, add it here too — otherwise programs that route to
    // the new syscall via runtime dispatch will SIGSEGV with a
    // dyld lookup of 0x0.
    const FFI_SYMS: &[&str] = &[
        "lean_sha256_agave",
        "lean_sha512",
        "lean_keccak256",
        "lean_blake3",
        "lean_secp256k1_recover",
        "lean_curve_validate_edwards",
        "lean_curve_validate_ristretto",
        "lean_curve_edwards_add",
        "lean_curve_edwards_sub",
        "lean_curve_edwards_mul",
        "lean_curve_ristretto_add",
        "lean_curve_ristretto_sub",
        "lean_curve_ristretto_mul",
        "lean_curve_edwards_msm",
        "lean_curve_ristretto_msm",
        "lean_bls12_381_g1_decompress",
        "lean_bls12_381_g2_decompress",
        "lean_bls12_381_pairing_map",
        "lean_alt_bn128_group_op",
        "lean_alt_bn128_compression",
        "lean_big_mod_exp",
        "lean_poseidon",
    ];
    let undersym_prefix = if cfg!(target_os = "macos") { "_" } else { "" };
    for sym in FFI_SYMS {
        println!(
            "cargo:rustc-link-arg=-Wl,-u,{}{}",
            undersym_prefix, sym
        );
    }
    println!("cargo:rustc-link-lib=static=leanbridge");

    // Export the binary's dynamic symbol table so the Lean dylibs'
    // `-undefined,dynamic_lookup` refs resolve at runtime.
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-rdynamic");
    }
    if cfg!(target_os = "macos") {
        println!("cargo:rustc-link-arg=-Wl,-export_dynamic");
    }

    // ─ Rebuild triggers. ──────────────────────────────────────────
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../Svm/Ffi.lean");
}

fn run_capture(cmd: &str, args: &[&str]) -> Option<String> {
    let out = Command::new(cmd).args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    String::from_utf8(out.stdout).ok()
}
