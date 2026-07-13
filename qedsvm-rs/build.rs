//! Compile the C glue (init/teardown wrappers) and delegate Lean
//! link-arg emission to the `qedsvm-buildscript` helper.
//!
//! Downstream consumers can call the same helper from their own
//! `build.rs` to inherit our Lake-output / Lean-toolchain link
//! setup without copy-pasting it (see issue #3 / PR #16).

use std::path::PathBuf;
use std::process::Command;

fn main() {
    // ─ Build our own glue C file (init/teardown wrappers). ────────
    //
    // We need the Lean include dir for `lean/lean.h`; ask the
    // toolchain directly rather than relying on the helper's
    // `cargo:include` output (which is only visible to *dependent*
    // crates' build scripts, not our own).
    let prefix = run_capture("lean", &["--print-prefix"])
        .expect("`lean --print-prefix` failed — is the Lean toolchain on PATH?");
    let prefix = prefix.trim();
    let lean_include = PathBuf::from(prefix).join("include");
    cc::Build::new()
        .file("csrc/init_glue.c")
        .include(&lean_include)
        .opt_level(2)
        .warnings(true)
        .compile("qedsvmglue");
    println!("cargo:rerun-if-changed=csrc/init_glue.c");

    // ─ Lake build output + Lean runtime linking. ──────────────────
    //
    // `qedsvm_root` is one level up from our manifest (the workspace
    // root containing `.lake/`). The helper does the rest — link
    // searches, rpath, force-loading the bridge archive, exporting
    // dynamic symbols, etc.
    let qedsvm_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("CARGO_MANIFEST_DIR has a parent")
        .to_path_buf();
    qedsvm_buildscript::emit_link_args(&qedsvm_root).expect("emit qedsvm link args");

    // ─ Local rebuild trigger. ─────────────────────────────────────
    println!("cargo:rerun-if-changed=build.rs");
}

fn run_capture(cmd: &str, args: &[&str]) -> Option<String> {
    let out = Command::new(cmd).args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    String::from_utf8(out.stdout).ok()
}
