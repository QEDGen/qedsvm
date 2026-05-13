//! Cross-engine differential test: same instruction through
//! `formal_svm::Svm` and `mollusk_svm::Mollusk`, with byte-level
//! assertions on every observable output.
//!
//! The fixture `tests/fixtures/noop.so` is a real
//! `cargo-build-sbf`-produced SBF ELF whose `.text` is exactly:
//!
//!     mov64 r0, 0    ; b7 00 00 00 00 00 00 00
//!     exit           ; 95 00 00 00 00 00 00 00
//!
//! That's the minimum cargo-build-sbf will emit — a hand-written
//! `extern "C" fn entrypoint(_input: *mut u8) -> u64 { 0 }` — and
//! it's still wrapped in a real Solana ELF (program headers,
//! `.dynsym`, `.shstrtab`, etc.) that agave's loader accepts.
//!
//! Build / rebuild:
//!     cd tests/fixtures/noop_src && cargo-build-sbf
//!     cp target/deploy/formal_svm_noop.so ../noop.so
//!
//! Run:  cargo test --features diff-mollusk

#![cfg(feature = "diff-mollusk")]

use formal_svm::{ProgramResult as FsProgramResult, Svm};
use mollusk_svm::result::ProgramResult as MlProgramResult;
use mollusk_svm::Mollusk;
use solana_account::{Account, AccountSharedData, ReadableAccount};
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

const NOOP_SO: &[u8] = include_bytes!("fixtures/noop.so");
const SOLANA_NOOP_SO: &[u8] = include_bytes!("fixtures/solana_noop.so");
/// `cargo-build-sbf` of a program that calls `msg!("hi")` and exits.
/// First fixture that exercises the `sol_log_` syscall + per-syscall
/// CU table (syscall_base_cost = 100 for a 2-byte message).
const LOGGER_SO: &[u8] = include_bytes!("fixtures/logger.so");
/// `cargo-build-sbf` of a program that reads a u64 from
/// `accounts[0].data[0..8]`, adds 1, writes it back, returns Ok.
/// First fixture that mutates account data — the cross-engine diff
/// verifies our `deserialize_account_writes` actually picks up the
/// program's write, byte-for-byte against mollusk.
const INCREMENTER_SO: &[u8] = include_bytes!("fixtures/incrementer.so");

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

/// Both engines accept the real cargo-build-sbf-produced ELF and
/// produce identical observable output for a trivial noop call.
#[test]
fn noop_program_matches_mollusk() {
    let program_id = pid(1);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    // ─ formal-svm side ────────────────────────────────────────────
    let mut fs = Svm::default();
    fs.add_program(&program_id, NOOP_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("formal-svm runs noop");

    // ─ Mollusk side ───────────────────────────────────────────────
    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    // ─ Diff ───────────────────────────────────────────────────────
    assert!(
        matches!(fs_r.program_result, FsProgramResult::Success),
        "formal-svm: expected Success, got {:?}", fs_r.program_result,
    );
    assert!(
        matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result,
    );
    assert_eq!(fs_r.return_data, m_r.return_data,
        "return_data diverged: ours={:?} mollusk={:?}", fs_r.return_data, m_r.return_data);
    assert_eq!(
        fs_r.resulting_accounts.len(),
        m_r.resulting_accounts.len(),
        "resulting_accounts count diverged",
    );
    // For accounts that are present in both lists, verify they
    // match field-by-field.
    for ((k_a, a_a), (k_b, a_b)) in
        fs_r.resulting_accounts.iter().zip(m_r.resulting_accounts.iter())
    {
        assert_eq!(k_a, k_b, "pubkey order divergence");
        assert_eq!(a_a.lamports(), a_b.lamports, "lamports diverged for {k_a}");
        assert_eq!(a_a.data(), a_b.data.as_slice(), "data diverged for {k_a}");
        assert_eq!(a_a.owner(), &a_b.owner, "owner diverged for {k_a}");
    }
    // CU equality: agave's program-runtime emits the same
    // "consumed 2 of 1.4M compute units" we report. (This is a
    // stricter check than the others — if the spec layer ever
    // diverges from agave's CU accounting for any instruction,
    // this catches it.)
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "compute_units_consumed diverged: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// The real `solana_program::entrypoint!`-using noop. This is the
/// program shape every published Solana program ships in: an
/// `entrypoint!` macro that deserializes the input buffer into
/// `(program_id, &[AccountInfo], &[u8])`, calls the user's
/// `process_instruction`, and converts the result back. ~1923 sBPF
/// instructions in `.text`. Cross-engine equality on this shape is
/// the actual "we conform to agave" claim.
#[test]
fn real_solana_program_entrypoint_noop_matches_mollusk() {
    let program_id = pid(3);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, SOLANA_NOOP_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("formal-svm runs");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SOLANA_NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    // Equal program result.
    match (&fs_r.program_result, &m_r.program_result) {
        (FsProgramResult::Success, MlProgramResult::Success) => {}
        (a, b) => panic!(
            "program_result diverged on real solana_program noop:\n  formal-svm: {a:?}\n  mollusk:    {b:?}",
        ),
    }
    // Equal return data.
    assert_eq!(fs_r.return_data, m_r.return_data,
        "return_data diverged");

    // With proper call/return semantics (Phase D — push retPc on
    // `.call_local`, pop on `.exit`), formal-svm runs the same
    // top-level instruction count as agave for this noop. We assert
    // exact CU equality, which catches any future regression that
    // off-by-one's the call frame logic.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "compute_units_consumed diverged on real solana_program noop: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// A program that actually calls a syscall (`sol_log_`). Validates
/// our per-syscall CU table by asserting both engines report the
/// exact same `compute_units_consumed` — equivalent to one
/// `syscall_base_cost = 100` charge on top of the framework
/// instructions both engines have to execute.
#[test]
fn logger_program_matches_mollusk() {
    let program_id = pid(4);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, LOGGER_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("formal-svm runs logger");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        LOGGER_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "formal-svm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    // Hard CU equality — passing this proves the syscall CU table
    // is at least correct for sol_log_ on a small message.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for msg!(\"hi\"): ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// First fixture that actually *mutates* account data. Reads a u64
/// from `accounts[0].data[0..8]`, adds 1, writes it back. Validates
/// that formal-svm's `deserialize_account_writes` picks up the
/// program's write, that it reports the new data identically to
/// mollusk, and that all other fields (lamports, owner, return data,
/// CU consumption) still match byte-for-byte.
#[test]
fn incrementer_program_matches_mollusk() {
    let program_id = pid(5);
    let acct_key = pid(6);
    // Account owned by the program so both engines permit the write
    // through the loader's ownership invariant check. The two engines
    // pull `solana-account` from different majors (4.x for us, 3.x for
    // mollusk), so we build the same shape twice from a shared spec.
    let lamports = 1_000_000u64;
    let data: Vec<u8> = vec![0u8; 16];

    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(acct_key, false)],
        data: vec![],
    };

    // Real on-chain CU budget. The default (200k) is plenty for this
    // program (mollusk consumes 321), but keep the budgets identical
    // across engines so any future budget-dependent path can't drift.
    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, INCREMENTER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("formal-svm runs incrementer");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        INCREMENTER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "formal-svm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");

    assert_eq!(fs_r.resulting_accounts.len(), 1, "formal-svm: expected 1 account back");
    assert_eq!(m_r.resulting_accounts.len(), 1, "mollusk: expected 1 account back");
    let (fs_key, fs_acct) = &fs_r.resulting_accounts[0];
    let (m_key, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(fs_key, &acct_key);
    assert_eq!(m_key, &acct_key);

    // The actual write-back claim: data[0..8] = 1u64.
    let mut want = vec![0u8; 16];
    want[..8].copy_from_slice(&1u64.to_le_bytes());
    assert_eq!(fs_acct.data(), want.as_slice(),
        "formal-svm did not record the increment: got {:?}", fs_acct.data());
    assert_eq!(m_acct.data.as_slice(), want.as_slice(),
        "mollusk did not record the increment: got {:?}", m_acct.data);

    assert_eq!(fs_acct.lamports(), m_acct.lamports, "lamports diverged");
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(), "data diverged");
    assert_eq!(fs_acct.owner(), &m_acct.owner, "owner diverged");

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for incrementer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Inputs reach the program: pass non-empty `instruction.data` and
/// confirm both engines accept it without divergence.
#[test]
fn noop_with_instruction_data_matches_mollusk() {
    let program_id = pid(2);
    let data = b"\x01\x02\x03\x04".to_vec();
    let ix = Instruction { program_id, accounts: vec![], data };

    let mut fs = Svm::default();
    fs.add_program(&program_id, NOOP_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("formal-svm runs");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success));
    assert!(matches!(m_r.program_result, MlProgramResult::Success));
    assert_eq!(fs_r.return_data, m_r.return_data);
}
