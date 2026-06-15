//! Tier-1 #2b precompile dispatch: Ed25519/secp256k1/secp256r1 sig-verify end-to-end via Lean Precompiles.dispatch.
//! Not diff-mollusk: mollusk's precompiles feature pin conflicts with the agave-4.0 graph.
//! CU pins: ED25519=2400, SECP256K1=6690, SECP256R1=4800.

use qedsvm::{ProgramResult, Svm};
use solana_account::{Account, AccountSharedData};
use solana_pubkey::Pubkey;

/// Counter-derived placeholder pubkey (Pubkey::new_unique is behind an `atomic` feature we don't enable).
fn dummy_pubkey() -> Pubkey {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(1);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&n.to_le_bytes());
    Pubkey::new_from_array(bytes)
}

fn precompile_native_account() -> AccountSharedData {
    AccountSharedData::from(Account {
        lamports: 1,
        data: vec![],
        owner: solana_sdk_ids::native_loader::id(),
        executable: true,
        rent_epoch: 0,
    })
}

#[test]
fn ed25519_precompile_accepts_valid_signature() {
    use ed25519_dalek::Signer;
    let mut rng = rand::thread_rng();
    let mut seed = [0u8; 32];
    rand::Rng::fill(&mut rng, &mut seed);
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&seed);

    let msg = b"qedsvm ed25519 precompile";
    let signature = signing_key.sign(msg).to_bytes();
    let pubkey_bytes = signing_key.verifying_key().to_bytes();

    let ix = solana_ed25519_program::new_ed25519_instruction_with_signature(
        msg,
        <&[u8; solana_ed25519_program::SIGNATURE_SERIALIZED_SIZE]>::try_from(&signature[..])
            .unwrap(),
        <&[u8; solana_ed25519_program::PUBKEY_SERIALIZED_SIZE]>::try_from(&pubkey_bytes[..])
            .unwrap(),
    );
    let ed_id = solana_sdk_ids::ed25519_program::id();
    let dummy = dummy_pubkey();

    let r = Svm::default()
        .process_instruction(&ix, &[
            (dummy, AccountSharedData::default()),
            (ed_id, precompile_native_account()),
        ])
        .expect("ed25519 precompile dispatches without harness error");

    assert!(matches!(r.program_result, ProgramResult::Success),
        "ed25519 precompile: expected Success, got {:?}", r.program_result);
    assert_eq!(r.compute_units_consumed, 2_400,
        "ed25519 per-sig CU: expected 2400, got {}", r.compute_units_consumed);
}

#[test]
fn ed25519_precompile_rejects_corrupted_signature() {
    use ed25519_dalek::Signer;
    let mut rng = rand::thread_rng();
    let mut seed = [0u8; 32];
    rand::Rng::fill(&mut rng, &mut seed);
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&seed);
    let msg = b"qedsvm ed25519 precompile";
    let mut signature = signing_key.sign(msg).to_bytes();
    signature[34] ^= 0x01; // flip a bit in the scalar — verify_strict must reject
    let pubkey_bytes = signing_key.verifying_key().to_bytes();
    let ix = solana_ed25519_program::new_ed25519_instruction_with_signature(
        msg,
        <&[u8; solana_ed25519_program::SIGNATURE_SERIALIZED_SIZE]>::try_from(&signature[..])
            .unwrap(),
        <&[u8; solana_ed25519_program::PUBKEY_SERIALIZED_SIZE]>::try_from(&pubkey_bytes[..])
            .unwrap(),
    );
    let r = Svm::default()
        .process_instruction(&ix, &[
            (dummy_pubkey(), AccountSharedData::default()),
            (solana_sdk_ids::ed25519_program::id(), precompile_native_account()),
        ])
        .expect("corrupted-sig precompile still dispatches");
    assert!(matches!(r.program_result, ProgramResult::Failure { exit_code: 1 }),
        "expected r0=1 on bad sig, got {:?}", r.program_result);
}

#[test]
fn secp256k1_precompile_accepts_valid_signature() {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    let mut sk_seed = [0u8; 32];
    rng.fill(&mut sk_seed);
    let secret_key = libsecp256k1::SecretKey::parse(&sk_seed)
        .expect("32 random bytes parse as secp256k1 secret");

    let msg = b"qedsvm secp256k1 precompile";
    let sk_bytes = secret_key.serialize();
    let (sig, recid) = solana_secp256k1_program::sign_message(&sk_bytes, msg)
        .expect("sign_message");
    let pk = libsecp256k1::PublicKey::from_secret_key(&secret_key);
    let uncompressed = pk.serialize();
    let mut uncompressed_64 = [0u8; 64];
    uncompressed_64.copy_from_slice(&uncompressed[1..65]);
    let eth_address =
        solana_secp256k1_program::eth_address_from_pubkey(&uncompressed_64);
    let ix = solana_secp256k1_program::new_secp256k1_instruction_with_signature(
        msg, &sig, recid, &eth_address,
    );
    let sk_id = solana_sdk_ids::secp256k1_program::id();
    let dummy = dummy_pubkey();
    let r = Svm::default()
        .process_instruction(&ix, &[
            (dummy, AccountSharedData::default()),
            (sk_id, precompile_native_account()),
        ])
        .expect("secp256k1 precompile dispatches");
    assert!(matches!(r.program_result, ProgramResult::Success),
        "secp256k1 precompile: expected Success, got {:?}", r.program_result);
    assert_eq!(r.compute_units_consumed, 6_690,
        "secp256k1 per-sig CU: expected 6690, got {}", r.compute_units_consumed);
}

#[test]
fn secp256r1_precompile_accepts_valid_signature() {
    use openssl::{
        bn::BigNumContext,
        ec::{EcGroup, EcKey, PointConversionForm},
        nid::Nid,
    };
    let group = EcGroup::from_curve_name(Nid::X9_62_PRIME256V1)
        .expect("P-256 curve");
    let secret_key = EcKey::generate(&group).expect("p256 keygen");
    let msg = b"qedsvm secp256r1 precompile";
    let sig = solana_secp256r1_program::sign_message(
        msg,
        &secret_key.private_key_to_der().unwrap(),
    ).expect("sign_message");
    let mut ctx = BigNumContext::new().unwrap();
    let pub_bytes = secret_key.public_key().to_bytes(
        secret_key.group(),
        PointConversionForm::COMPRESSED,
        &mut ctx,
    ).expect("compressed pubkey");
    let mut pubkey =
        [0u8; solana_secp256r1_program::COMPRESSED_PUBKEY_SERIALIZED_SIZE];
    pubkey.copy_from_slice(&pub_bytes);
    let ix = solana_secp256r1_program::new_secp256r1_instruction_with_signature(
        msg, &sig, &pubkey,
    );
    let r1_id = solana_sdk_ids::secp256r1_program::id();
    let dummy = dummy_pubkey();
    let r = Svm::default()
        .process_instruction(&ix, &[
            (dummy, AccountSharedData::default()),
            (r1_id, precompile_native_account()),
        ])
        .expect("secp256r1 precompile dispatches");
    assert!(matches!(r.program_result, ProgramResult::Success),
        "secp256r1 precompile: expected Success, got {:?}", r.program_result);
    assert_eq!(r.compute_units_consumed, 4_800,
        "secp256r1 per-sig CU: expected 4800, got {}", r.compute_units_consumed);
}

#[test]
fn unknown_pid_does_not_match_precompile_path() {
    let pid = dummy_pubkey(); // unknown pid must not route through precompile path — expect UnknownProgram
    let ix = solana_instruction::Instruction {
        program_id: pid, accounts: vec![], data: vec![1, 2, 3],
    };
    let err = Svm::default().process_instruction(&ix, &[])
        .expect_err("unknown pid must surface SvmError, not run precompile");
    assert!(
        matches!(err, qedsvm::SvmError::UnknownProgram(p) if p == pid),
        "unexpected error: {err:?}",
    );
}
