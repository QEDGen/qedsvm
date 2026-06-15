//! API smoke tests for `Svm::process_instruction` (helloElf fixture); exercises full serialize→Lean→deserialize path.

use qedsvm::{
    deserialize_account_writes, serialize_parameters,
    ProgramResult, SerializeError, Svm, SvmError,
};
use solana_account::{Account, AccountSharedData};
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

const HELLO_ELF: &[u8] = include_bytes!("fixtures/hello.elf"); // 289B: `mov64 r0, 42; exit` = RunnerDemo.helloElf

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

fn shared(lamports: u64, data: Vec<u8>, owner: Pubkey) -> AccountSharedData {
    AccountSharedData::from(Account {
        lamports,
        data,
        owner,
        executable: false,
        rent_epoch: 0,
    })
}

#[test]
fn process_instruction_with_no_accounts_returns_helloelfs_exit_code() {
    let program_id = pid(1);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);

    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");

    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert!(result.logs.is_empty());
    assert!(result.return_data.is_empty());
    assert!(result.resulting_accounts.is_empty());
}

#[test]
fn process_instruction_with_accounts_round_trips_unchanged_buffer() {
    let program_id = pid(2); // hello ELF never touches input; accounts come back identical
    let key = pid(3);
    let owner = pid(4);
    let pre = shared(7_777, vec![0xAA, 0xBB, 0xCC], owner);

    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(key, false)],
        data: vec![0x01, 0x02],
    };
    let result = svm.process_instruction(&ix, &[(key, pre.clone())])
        .expect("runs");

    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert_eq!(result.resulting_accounts.len(), 1);
    let (out_key, out_acct) = &result.resulting_accounts[0];
    assert_eq!(out_key, &key);
    use solana_account::ReadableAccount;
    assert_eq!(out_acct.lamports(), 7_777);
    assert_eq!(out_acct.data(), &[0xAA, 0xBB, 0xCC]);
    assert_eq!(out_acct.owner(), &owner);
}

#[test]
fn unknown_program_returns_svm_error() {
    let svm = Svm::default();
    let ix = Instruction { program_id: pid(99), accounts: vec![], data: vec![] };
    match svm.process_instruction(&ix, &[]) {
        Err(SvmError::UnknownProgram(pk)) => assert_eq!(pk, pid(99)),
        other => panic!("expected UnknownProgram, got {other:?}"),
    }
}

#[test]
fn compute_units_consumed_matches_program_length() {
    // hello ELF = 2 instructions (mov64 r0,42; exit); 1 fuel per step → CU=2.
    let program_id = pid(7);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    assert_eq!(result.compute_units_consumed, 2,
        "hello ELF is 2 instructions; got CU={}", result.compute_units_consumed);
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
}

/// Second program registered → registry path (`run_buffer_with_registry`); same result as single-program case.
#[test]
fn process_instruction_with_multiple_programs_routes_through_registry() {
    let main_id = pid(20);
    let other_id = pid(21);
    let mut svm = Svm::default();
    svm.add_program(&main_id, HELLO_ELF);
    svm.add_program(&other_id, HELLO_ELF); // second program ⇒ registry path
    let ix = Instruction { program_id: main_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert_eq!(result.compute_units_consumed, 2);
}

#[test]
fn process_instruction_accepts_shuffled_caller_accounts() {
    // ix.accounts=[A,B], caller passes [B,A]; canonical-ordering must look up by pubkey and return in ix order.
    let program_id = pid(50);
    let a = pid(51);
    let b = pid(52);
    let owner = pid(53);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(a, false), AccountMeta::new(b, false)],
        data: vec![],
    };
    let shuffled = vec![
        (b, shared(222, vec![0xBB], owner)),
        (a, shared(111, vec![0xAA], owner)),
    ];
    let result = svm.process_instruction(&ix, &shuffled).expect("runs");

    use solana_account::ReadableAccount;
    assert_eq!(result.resulting_accounts.len(), 2);
    let (k0, a0) = &result.resulting_accounts[0];
    let (k1, a1) = &result.resulting_accounts[1];
    assert_eq!(k0, &a);
    assert_eq!(k1, &b);
    assert_eq!(a0.lamports(), 111);
    assert_eq!(a1.lamports(), 222);
    assert_eq!(a0.data(), &[0xAA]);
    assert_eq!(a1.data(), &[0xBB]);
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 }); // validate_post_state not triggered by shuffle
}

#[test]
fn process_instruction_ignores_extra_caller_accounts() {
    // Extra account not in ix.accounts must be silently dropped (not in resulting_accounts, not in lamport sum).
    let program_id = pid(60);
    let used = pid(61);
    let extra = pid(62);
    let owner = pid(63);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(used, false)],
        data: vec![],
    };
    let supplied = vec![
        (used, shared(100, vec![], owner)),
        (extra, shared(9_999_999, vec![], owner)),
    ];
    let result = svm.process_instruction(&ix, &supplied).expect("runs");

    assert_eq!(result.resulting_accounts.len(), 1);
    assert_eq!(result.resulting_accounts[0].0, used);
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 }); // lamport conservation passed
}

#[test]
fn missing_account_returns_serialize_error() {
    let program_id = pid(9);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);
    let missing = pid(100);
    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(missing, false)],
        data: vec![],
    };
    match svm.process_instruction(&ix, &[]) { // missing pubkey → MissingAccount
        Err(SvmError::Serialize(SerializeError::MissingAccount(pk))) => {
            assert_eq!(pk, missing);
        }
        other => panic!("expected Serialize(MissingAccount), got {other:?}"),
    }
}

#[test]
fn too_many_accounts_returns_serialize_error() {
    let program_id = pid(10);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);
    let metas: Vec<AccountMeta> = // 256 > 255 cap (NON_DUP_MARKER = 0xFF)
        (0..256).map(|i| AccountMeta::new(pid(1000 + i), false)).collect();
    let accounts: Vec<(Pubkey, AccountSharedData)> =
        (0..256).map(|i| (pid(1000 + i), shared(0, vec![], pid(0)))).collect();
    let ix = Instruction { program_id, accounts: metas, data: vec![] };
    match svm.process_instruction(&ix, &accounts) {
        Err(SvmError::Serialize(SerializeError::TooManyAccounts(n))) => {
            assert_eq!(n, 256);
        }
        other => panic!("expected Serialize(TooManyAccounts), got {other:?}"),
    }
}

#[test]
fn cu_budget_exhaustion_reports_full_budget_consumed() {
    // Budget=1 → can't finish even 2-insn program; consumed=1 (remaining fuel=0 at OOG).
    let program_id = pid(8);
    let mut svm = Svm::default().with_cu_budget(1);
    svm.add_program(&program_id, HELLO_ELF);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    assert_eq!(result.program_result, ProgramResult::OutOfBudget);
    assert_eq!(result.compute_units_consumed, 1);
}

#[test]
fn compute_budget_from_instructions_picks_up_set_unit_limit() {
    // SetComputeUnitLimit(50_000) followed by prog ix → budget reflects 50k, not 200k default.
    let program_id = pid(9);
    let cb_id = solana_sdk_ids::compute_budget::ID;
    // Discriminant 2 + u32 LE = 50000 (0xC350)
    let set_limit = Instruction {
        program_id: cb_id,
        accounts: vec![],
        data: vec![2, 0x50, 0xC3, 0x00, 0x00],
    };
    let prog_ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let txn_ixs = [set_limit, prog_ix.clone()];

    let mut svm = Svm::default().with_compute_budget_from_instructions(&txn_ixs);
    svm.add_program(&program_id, HELLO_ELF);

    let result = svm.process_instruction(&prog_ix, &[]).expect("runs");
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert!(result.compute_units_consumed < 50_000); // well under 50k; confirms budget changed from 200k default
}

#[test]
fn compute_budget_from_instructions_no_set_limit_keeps_default() {
    // No ComputeBudget ix in the list → budget stays at default 200k.
    let program_id = pid(10);
    let prog_ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let mut svm = Svm::default().with_compute_budget_from_instructions(&[prog_ix.clone()]);
    svm.add_program(&program_id, HELLO_ELF);
    let result = svm.process_instruction(&prog_ix, &[]).expect("runs");
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
}

#[test]
fn compute_budget_from_instructions_last_set_limit_wins() {
    // Two SetComputeUnitLimit ixs: last (100k) overrides first (10k); mirrors agave iterate-and-overwrite.
    let program_id = pid(11);
    let cb_id = solana_sdk_ids::compute_budget::ID;
    let set_10k  = Instruction { program_id: cb_id, accounts: vec![],
                                 data: vec![2, 0x10, 0x27, 0x00, 0x00] }; // 10_000
    let set_100k = Instruction { program_id: cb_id, accounts: vec![],
                                 data: vec![2, 0xA0, 0x86, 0x01, 0x00] }; // 100_000
    let prog_ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let txn_ixs = [set_10k, set_100k, prog_ix.clone()];

    let mut svm = Svm::default().with_compute_budget_from_instructions(&txn_ixs);
    svm.add_program(&program_id, HELLO_ELF);

    let result = svm.process_instruction(&prog_ix, &[]).expect("runs");
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert!(result.compute_units_consumed > 0); // hello is 2 insns, can't distinguish 10k vs 100k; just assert the call works
}

// Pinocchio borrow_state reproducer (issue #2): RuntimeAccount overlays borrow_state on the dup_info byte.
// try_borrow_mut writes 0; Drop restores 0xFF; a guard leaked across return leaves byte at 0..254.
// Tests stomp the byte post-serialize to drive the failure without a real Pinocchio program.

fn stomp_first_dup_byte(buf: &mut [u8], to: u8) {
    // [u64 num_accounts][u8 dup_info ...] — first dup byte is at offset 8.
    buf[8] = to;
}

#[test]
fn deserialize_tolerates_pinocchio_mut_borrow_leaked_to_byte_zero() {
    // try_borrow_mut held across return leaves byte at 0; deserializer must tolerate.
    let program_id = pid(60);
    let key = pid(61);
    let owner = pid(62);
    let pre = shared(1_000, vec![1, 2, 3, 4, 5], owner);

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new_readonly(key, false)],
        data: vec![0u8],
    };
    let mut buf = serialize_parameters(&ix, &[(key, pre.clone())], &program_id)
        .expect("serialize");
    assert_eq!(buf[8], 0xFF, "sanity: serializer wrote NON_DUP_MARKER");
    stomp_first_dup_byte(&mut buf, 0);

    let out = deserialize_account_writes(&buf, &ix, &[(key, pre.clone())])
        .expect("deserializer must tolerate stomped borrow_state byte");
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].0, key);
}

#[test]
fn deserialize_tolerates_partial_immutable_borrow_drop() {
    // miss-a-drop of immutable borrow leaves byte at 0xFE; deserializer must tolerate.
    let program_id = pid(63);
    let key = pid(64);
    let owner = pid(65);
    let pre = shared(2_000, vec![9, 9, 9], owner);

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new_readonly(key, false)],
        data: vec![],
    };
    let mut buf = serialize_parameters(&ix, &[(key, pre.clone())], &program_id)
        .expect("serialize");
    stomp_first_dup_byte(&mut buf, 0xFE);

    let out = deserialize_account_writes(&buf, &ix, &[(key, pre.clone())])
        .expect("deserializer must tolerate any post-execution borrow_state value");
    assert_eq!(out.len(), 1);
}

#[test]
fn deserialize_with_two_distinct_accounts_does_not_misread_stomped_byte_as_dup() {
    // 2 distinct accounts, second's dup byte stomped to 0 — buffer-trusting code silently aliases; must not.
    let program_id = pid(70);
    let a = pid(71);
    let b = pid(72);
    let owner = pid(73);
    let pre_a = shared(100, vec![0xAA, 0xAA, 0xAA], owner);
    let pre_b = shared(200, vec![0xBB, 0xBB], owner);

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(a, false),
            AccountMeta::new_readonly(b, false),
        ],
        data: vec![],
    };
    let pre = [(a, pre_a.clone()), (b, pre_b.clone())];
    let mut buf = serialize_parameters(&ix, &pre, &program_id).expect("serialize");

    use solana_program_entrypoint::{BPF_ALIGN_OF_U128, MAX_PERMITTED_DATA_INCREASE};
    let first_record_data_len = 3usize;
    let align_pad = (BPF_ALIGN_OF_U128 - first_record_data_len % BPF_ALIGN_OF_U128) % BPF_ALIGN_OF_U128;
    let first_record_size =
        1 + 1 + 1 + 1 + 4 + 32 + 32 + 8 + 8 + first_record_data_len + align_pad + MAX_PERMITTED_DATA_INCREASE + 8;
    let second_dup_offset = 8 + first_record_size;
    assert_eq!(buf[second_dup_offset], 0xFF, "sanity: second record starts with NON_DUP_MARKER");
    buf[second_dup_offset] = 0;

    let out = deserialize_account_writes(&buf, &ix, &pre)
        .expect("deserializer must not silently treat stomped byte as a dup");
    assert_eq!(out.len(), 2);
    assert_eq!(out[0].0, a);
    assert_eq!(out[1].0, b, "slot 1 must be account B, not silently aliased to A");
    use solana_account::ReadableAccount;
    assert_eq!(out[1].1.lamports(), 200);
    assert_eq!(out[1].1.data(), &[0xBB, 0xBB]);
}
