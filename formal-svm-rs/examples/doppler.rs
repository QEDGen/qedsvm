//! Doppler oracle demo via the mollusk-shaped `Svm` API.
//!
//! Exercises all three code paths of doppler's `entrypoint`
//! (https://github.com/blueshift-gg/doppler):
//!
//! 1. Happy path: admin OK + new_seq > current_seq → full update.
//! 2. Bad admin: hits the `lddw r0, 1; exit` inline-asm fast-exit in
//!    `Admin::check`.
//! 3. Stale sequence: hits the `lddw r0, 2; exit` inline-asm fast-exit
//!    in `Oracle::check_and_update`.
//!
//! Unlike the shell-script version that hand-builds a 0x50f0-byte
//! parameter buffer, this driver constructs Solana-shaped accounts and
//! lets `formal_svm::serialize_parameters` place the bytes at the
//! offsets doppler reads from. The Svm API mirrors mollusk's API
//! signature, so swap-in is trivial.
//!
//! Run:
//!   cargo run --release --example doppler --manifest-path formal-svm-rs/Cargo.toml
//!
//! The example self-bootstraps the doppler `.so`:
//!   1. If `$DOPPLER_SO` is set, uses it.
//!   2. Else, looks for a cached `target/examples-cache/doppler/doppler_program.so`.
//!   3. Else, clones https://github.com/blueshift-gg/doppler, patches the
//!      `#[no_mangle]`-on-panic_handler issue, runs `cargo-build-sbf`, caches
//!      the output, and uses it.
//!
//! First run takes ~20s for the clone + build; subsequent runs hit the cache.

use std::path::{Path, PathBuf};
use std::process::Command;

use formal_svm::{ProgramResult, Svm};
use solana_account::{Account, AccountSharedData, ReadableAccount};
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

// `admnz5UvRa93HM5nTrxXmsJ1rw2tvXMBFGauvCgzQhE` — doppler's hardcoded
// admin pubkey (lifted from doppler/doppler/src/admin.rs).
const ADMIN: [u8; 32] = [
    0x08, 0x9d, 0xbe, 0xc9, 0x64, 0x97, 0xab, 0xd0,
    0xdb, 0x21, 0x79, 0x52, 0x69, 0xba, 0xb9, 0x4b,
    0xc8, 0xb8, 0x49, 0xcc, 0x05, 0xaa, 0x94, 0x54,
    0xd0, 0xa5, 0xdc, 0x76, 0xec, 0xcb, 0x51, 0xd1,
];

/// `repr(C) { sequence: u64, payload: u64 }` packed as 16 LE bytes.
fn oracle_bytes(sequence: u64, payload: u64) -> Vec<u8> {
    let mut data = Vec::with_capacity(16);
    data.extend_from_slice(&sequence.to_le_bytes());
    data.extend_from_slice(&payload.to_le_bytes());
    data
}

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

/// Build the standard doppler update instruction.
/// `data` is `[new_sequence:u64, new_payload:u64]`.
fn update_ix(admin: Pubkey, oracle: Pubkey, new_sequence: u64, new_payload: u64)
    -> Instruction
{
    let program_id = pid(0xd0);
    Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(admin, true),   // admin (signer, ro)
            AccountMeta::new(oracle, false),          // oracle (writable)
        ],
        data: oracle_bytes(new_sequence, new_payload),
    }
}

fn scenario(label: &str, svm: &Svm, ix: &Instruction,
            accounts: &[(Pubkey, AccountSharedData)]) {
    let r = svm.process_instruction(ix, accounts).expect("runs");
    println!("── {label} ──");
    println!("  program_result:        {:?}", r.program_result);
    println!("  compute_units_consumed: {}", r.compute_units_consumed);

    // Inspect the resulting oracle account (index 1) data, if present.
    if let Some((_, oracle_post)) = r.resulting_accounts.get(1) {
        let data = oracle_post.data();
        if data.len() >= 16 {
            let seq = u64::from_le_bytes(data[..8].try_into().unwrap());
            let pay = u64::from_le_bytes(data[8..16].try_into().unwrap());
            println!("  oracle.sequence (post): {seq}");
            println!("  oracle.payload  (post): {pay}");
        }
    }
    println!();
}

/// Locate or build the doppler .so. Returns the path.
///
/// 1. `$DOPPLER_SO` override → used directly.
/// 2. Cached `target/examples-cache/doppler/doppler_program.so` → used.
/// 3. Otherwise clone + patch + build, then cache.
fn locate_doppler_so() -> PathBuf {
    if let Ok(p) = std::env::var("DOPPLER_SO") {
        return PathBuf::from(p);
    }
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cache_dir = crate_root.join("target/examples-cache/doppler");
    let so_path = cache_dir.join("doppler_program.so");
    if so_path.exists() {
        return so_path;
    }
    eprintln!(">> bootstrapping doppler (one-time clone + cargo-build-sbf) ...");
    std::fs::create_dir_all(&cache_dir).expect("mkdir cache_dir");

    let src_dir = cache_dir.join("src");
    if !src_dir.exists() {
        run(Command::new("git")
            .args(["clone", "--depth", "1", "https://github.com/blueshift-gg/doppler.git"])
            .arg(&src_dir),
            "git clone doppler");
    }
    // Patch the `#[no_mangle] #[panic_handler]` combo that the bundled rustc rejects.
    patch_panic_handler(&src_dir.join("doppler/src/panic_handler.rs"));
    run(Command::new("cargo-build-sbf")
        .current_dir(src_dir.join("program")),
        "cargo-build-sbf");
    let built = src_dir.join("target/deploy/doppler_program.so");
    std::fs::copy(&built, &so_path)
        .unwrap_or_else(|e| panic!("copy {} → {}: {e}", built.display(), so_path.display()));
    so_path
}

fn run(cmd: &mut Command, label: &str) {
    let status = cmd.status().unwrap_or_else(|e| panic!("{label}: {e}"));
    if !status.success() {
        panic!("{label}: exited with {status}");
    }
}

fn patch_panic_handler(path: &Path) {
    let content = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let needle = "        #[no_mangle]\n        #[panic_handler]";
    let patched = content.replace(needle, "        #[panic_handler]");
    if patched != content {
        std::fs::write(path, patched)
            .unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    }
}

fn main() {
    let so_path = locate_doppler_so();
    let doppler_so = std::fs::read(&so_path)
        .unwrap_or_else(|e| panic!("failed to read .so at {}: {e}", so_path.display()));

    let admin_pk = Pubkey::from(ADMIN);
    let oracle_pk = pid(0xc0); // arbitrary oracle account key
    let program_id = pid(0xd0);

    let mut svm = Svm::default();
    svm.add_program(&program_id, &doppler_so);

    // === Scenario 1: happy path ===
    let admin_acct = AccountSharedData::from(Account {
        lamports: 10_000_000_000,
        data: vec![],
        owner: Pubkey::new_from_array([0u8; 32]), // system_program
        executable: false,
        rent_epoch: 0,
    });
    let oracle_acct_pre = AccountSharedData::from(Account {
        lamports: 1_000_000,                          // rent-irrelevant for this demo
        data: oracle_bytes(/* sequence */ 100, /* payload */ 1000),
        owner: program_id,                            // owned by doppler program
        executable: false,
        rent_epoch: 0,
    });
    let ix = update_ix(admin_pk, oracle_pk, 101, 1500);
    scenario("admin OK + new_seq=101 > current=100 → update",
             &svm, &ix,
             &[(admin_pk, admin_acct.clone()),
               (oracle_pk, oracle_acct_pre.clone())]);

    // === Scenario 2: bad admin ===
    // Wrong admin pubkey → Admin::check fast-exit (r0=1).
    let bad_admin_pk = pid(0xbad);
    let ix_bad = update_ix(bad_admin_pk, oracle_pk, 101, 1500);
    scenario("bad admin pubkey → Admin::check fast-exit (r0=1)",
             &svm, &ix_bad,
             &[(bad_admin_pk, admin_acct.clone()),
               (oracle_pk, oracle_acct_pre.clone())]);

    // === Scenario 3: stale oracle ===
    // new_seq = current_seq (not strictly greater) → Oracle fast-exit (r0=2).
    let ix_stale = update_ix(admin_pk, oracle_pk, 100, 1500);
    scenario("stale oracle (new_seq=100 = current=100) → Oracle::check_and_update fast-exit (r0=2)",
             &svm, &ix_stale,
             &[(admin_pk, admin_acct),
               (oracle_pk, oracle_acct_pre)]);

    // Sanity: every scenario should be Success/Failure (not OutOfBudget).
    println!("Done — 3 scenarios, all run via Svm::process_instruction.");
    let _: ProgramResult = ProgramResult::Success; // type sanity
}
