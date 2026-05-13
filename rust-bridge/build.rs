//! Compile `lean_glue.c` and link it into the staticlib.
//!
//! Discovers Lean's include directory by shelling out to
//! `lean --print-prefix`. That matches Lake's behavior (Lake uses the
//! `lean` on PATH).

use std::process::Command;

fn main() {
    let output = Command::new("lean")
        .arg("--print-prefix")
        .output()
        .expect("failed to run `lean --print-prefix` — is `lean` on PATH?");
    if !output.status.success() {
        panic!(
            "lean --print-prefix exited with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let prefix = String::from_utf8(output.stdout)
        .expect("lean --print-prefix produced non-UTF8 output");
    let prefix = prefix.trim();
    let include_dir = format!("{}/include", prefix);

    cc::Build::new()
        .file("lean_glue.c")
        .include(&include_dir)
        .opt_level(2)
        .warnings(true)
        .compile("leanglue");

    println!("cargo:rerun-if-changed=lean_glue.c");
    println!("cargo:rerun-if-changed=build.rs");
}
