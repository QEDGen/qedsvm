//! Blueshift hand-written sBPF programs demo via the low-level
//! `run_buffer` API. Covers the two branching programs that use
//! bespoke (non-Solana-standard) input layouts:
//!
//! - `asm-slippage`: reads MINIMUM_BALANCE @ 0x2918 and
//!   TOKEN_ACCOUNT_BALANCE @ 0x00a0; logs an error + returns 1 when
//!   the token balance is below the minimum.
//! - `asm-timeout`: reads CLOCK_SYSVAR_SLOT @ 0x0060 and
//!   INSTRUCTION_TARGET_SLOT @ 0x2898; returns the current slot if
//!   in window, else returns error code 1.
//!
//! Both programs were hand-written in sBPF assembly and don't use the
//! Solana entrypoint parameter serialization — they index directly
//! into the raw input region. The `run_buffer` API takes raw bytes,
//! mirroring how the blueshift authors wrote the source.
//!
//! `asm-hello` and `asm-memo` are skipped — they exercise
//! `sol_log_` and trivial loads, fully covered by the shell demo.
//!
//! Run:
//!   # 1. Clone https://github.com/blueshift-gg/asm (or export BLUESHIFT).
//!   # 2. cd asm-slippage && cargo-build-sbf  (and same for asm-timeout).
//!   # 3. Run:
//!   BLUESHIFT=/path/to/blueshift \
//!     cargo run --release --example blueshift_asm \
//!       --manifest-path formal-svm-rs/Cargo.toml

use formal_svm::{run_buffer, ExitOutcome};

fn load_so(prog: &str, blueshift: &str) -> Vec<u8> {
    let path = format!("{blueshift}/asm/asm-{prog}/deploy/asm-{prog}.so");
    std::fs::read(&path).unwrap_or_else(|e| {
        eprintln!("failed to read {path}: {e}");
        std::process::exit(1);
    })
}

fn run(label: &str, so: &[u8], input: &[u8]) {
    let r = run_buffer(so, input, 1_400_000).expect("decode succeeds");
    println!("── {label} ──");
    println!("  outcome: {:?}", r.outcome);
    println!("  cu:      {}", r.compute_units_consumed);
    if !r.logs.is_empty() {
        for (i, line) in r.logs.iter().enumerate() {
            // Best-effort utf8; logs are bytes.
            let s = String::from_utf8_lossy(line);
            println!("  log[{i}]: {s}");
        }
    }
    println!();
}

/// asm-slippage input layout (lifted from
/// blueshift/asm/asm-slippage/src/asm-slippage/asm-slippage.s):
/// - 0x00a0: TOKEN_ACCOUNT_BALANCE (u64)
/// - 0x2918: MINIMUM_BALANCE      (u64)
fn slippage_input(avail: u64, min: u64) -> Vec<u8> {
    let mut buf = vec![0u8; 0x2920];
    buf[0x00a0..0x00a8].copy_from_slice(&avail.to_le_bytes());
    buf[0x2918..0x2920].copy_from_slice(&min.to_le_bytes());
    buf
}

/// asm-timeout input layout:
/// - 0x0060: CLOCK_SYSVAR_SLOT          (u64) → "current slot"
/// - 0x2898: INSTRUCTION_TARGET_SLOT    (u64) → "target slot"
fn timeout_input(current: u64, target: u64) -> Vec<u8> {
    let mut buf = vec![0u8; 0x28a0];
    buf[0x0060..0x0068].copy_from_slice(&current.to_le_bytes());
    buf[0x2898..0x28a0].copy_from_slice(&target.to_le_bytes());
    buf
}

fn main() {
    let blueshift = std::env::var("BLUESHIFT").unwrap_or_else(|_| {
        format!("{}/code/blueshift", std::env::var("HOME").unwrap_or_default())
    });

    let slippage_so = load_so("slippage", &blueshift);
    let timeout_so = load_so("timeout", &blueshift);

    println!("=== asm-slippage ===\n");
    run("avail=1000, min=500 → in-window exit",
        &slippage_so, &slippage_input(1000, 500));
    run("avail=100,  min=500 → slippage exceeded (logs error, r0=1)",
        &slippage_so, &slippage_input(100, 500));

    println!("=== asm-timeout ===\n");
    run("current=50,  target=100 → in window (r0 = current slot)",
        &timeout_so, &timeout_input(50, 100));
    run("current=100, target=50  → timed out (r0=1)",
        &timeout_so, &timeout_input(100, 50));

    // Echo the type so the import isn't dead code if the example
    // is run with the logs lib stripped out.
    let _: ExitOutcome = ExitOutcome::Halted(0);
}
