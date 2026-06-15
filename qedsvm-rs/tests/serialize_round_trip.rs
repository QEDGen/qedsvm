//! Conformance test: serialize via `qedsvm::serialize_parameters`, deserialize via `solana_program_entrypoint::deserialize`.
//! Any width/padding/alignment deviation either crashes the deserializer or produces wrong values.

use qedsvm::serialize_parameters;
use solana_account::{Account, AccountSharedData};
use solana_account_info::AccountInfo;
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

/// 8-byte-aligned wrapper so the BPF deserializer's `*const u64` reads are well-defined.
#[repr(C, align(8))]
struct AlignedBuf {
    bytes: Vec<u8>,
}

unsafe fn deserialize_via_solana<'a>(
    buf: &'a mut AlignedBuf,
) -> (&'a Pubkey, Vec<AccountInfo<'a>>, &'a [u8]) {
    // The official deserializer reads from a `*mut u8` pointer.
    let ptr: *mut u8 = buf.bytes.as_mut_ptr();
    unsafe { solana_program_entrypoint::deserialize(ptr) }
}

fn make_ix(metas: Vec<AccountMeta>, data: Vec<u8>, program_id: Pubkey) -> Instruction {
    Instruction { program_id, accounts: metas, data }
}

/// Counter-derived unique pubkey (avoids the `rand`-gated `new_unique` feature).
fn unique_pubkey() -> Pubkey {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(1);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&n.to_le_bytes());
    Pubkey::from(bytes)
}

fn shared(lamports: u64, data: Vec<u8>, owner: Pubkey, executable: bool) -> AccountSharedData {
    AccountSharedData::from(Account {
        lamports,
        data,
        owner,
        executable,
        rent_epoch: 0,
    })
}

#[test]
fn single_account_round_trips() {
    let program_id = unique_pubkey();
    let key = unique_pubkey();
    let owner = unique_pubkey();
    let ix = make_ix(
        vec![AccountMeta::new(key, true)],
        vec![0xAA, 0xBB, 0xCC],
        program_id,
    );
    let accounts = vec![(key, shared(1_000_000, vec![1, 2, 3, 4, 5], owner, false))];

    let mut buf = AlignedBuf {
        bytes: serialize_parameters(&ix, &accounts, &program_id).expect("valid inputs"),
    };

    let (pid_out, infos, data_out) = unsafe { deserialize_via_solana(&mut buf) };
    assert_eq!(pid_out, &program_id);
    assert_eq!(infos.len(), 1);
    assert_eq!(infos[0].key, &key);
    assert_eq!(infos[0].owner, &owner);
    assert!(infos[0].is_signer);
    assert!(infos[0].is_writable);
    assert!(!infos[0].executable);
    assert_eq!(**infos[0].lamports.borrow(), 1_000_000);
    assert_eq!(&**infos[0].data.borrow(), &[1u8, 2, 3, 4, 5]);
    assert_eq!(data_out, &[0xAA, 0xBB, 0xCC]);
}

#[test]
fn multiple_distinct_accounts_round_trip() {
    let program_id = unique_pubkey();
    let owner = unique_pubkey();
    let k1 = unique_pubkey();
    let k2 = unique_pubkey();
    let k3 = unique_pubkey();
    let ix = make_ix(
        vec![
            AccountMeta::new(k1, true),
            AccountMeta::new_readonly(k2, false),
            AccountMeta::new(k3, false),
        ],
        b"hello".to_vec(),
        program_id,
    );
    let accounts = vec![
        (k1, shared(100, vec![], owner, false)),
        (k2, shared(200, vec![0xDE, 0xAD], owner, true)),
        (k3, shared(300, (0..50).collect(), owner, false)),
    ];

    let mut buf = AlignedBuf {
        bytes: serialize_parameters(&ix, &accounts, &program_id).expect("valid inputs"),
    };
    let (pid_out, infos, data_out) = unsafe { deserialize_via_solana(&mut buf) };

    assert_eq!(pid_out, &program_id);
    assert_eq!(infos.len(), 3);
    assert_eq!(infos[0].key, &k1);
    assert!(infos[0].is_signer && infos[0].is_writable);
    assert_eq!(&**infos[0].data.borrow(), &[] as &[u8]);
    assert_eq!(infos[1].key, &k2);
    assert!(!infos[1].is_signer && !infos[1].is_writable);
    assert!(infos[1].executable);
    assert_eq!(&**infos[1].data.borrow(), &[0xDE, 0xAD]);
    assert_eq!(infos[2].key, &k3);
    assert_eq!(infos[2].data.borrow().len(), 50);
    assert_eq!(data_out, b"hello");
}

#[test]
fn duplicate_account_meta_compresses() {
    let program_id = unique_pubkey(); // same pubkey twice → second occurrence emits dup-marker form
    let owner = unique_pubkey();
    let k1 = unique_pubkey();
    let ix = make_ix(
        vec![
            AccountMeta::new(k1, true),
            AccountMeta::new(k1, true),  // same pubkey — should become dup
        ],
        vec![],
        program_id,
    );
    let accounts = vec![(k1, shared(42, vec![9, 9, 9], owner, false))];

    let bytes = serialize_parameters(&ix, &accounts, &program_id).expect("valid inputs");
    assert_eq!(bytes[0..8], 2u64.to_le_bytes());  // num_accounts = 2
    assert_eq!(bytes[8], 0xFF);                    // first is non-dup; data_len=3 align_pad=5
    let first_acct_len = 1 + 1 + 1 + 1 + 4 + 32 + 32 + 8 + 8 + 3 + 5 + 10240 + 8;
    let dup_byte_off = 8 + first_acct_len;
    assert_eq!(bytes[dup_byte_off], 0);  // dup → index 0
    assert_eq!(bytes[dup_byte_off + 1..dup_byte_off + 8], [0u8; 7]);

    let mut buf = AlignedBuf { bytes };
    let (_pid, infos, _data) = unsafe { deserialize_via_solana(&mut buf) };
    assert_eq!(infos.len(), 2);
    assert_eq!(infos[0].key, &k1);
    assert_eq!(infos[1].key, &k1);
}

#[test]
fn known_offsets_match_spec() {
    // Exact byte-level spot check on deterministic input; catches padding regressions the round-trip test misses.
    let program_id = Pubkey::from([7u8; 32]);
    let key = Pubkey::from([1u8; 32]);
    let owner = Pubkey::from([2u8; 32]);
    let ix = make_ix(
        vec![AccountMeta::new_readonly(key, false)],
        vec![0x10],
        program_id,
    );
    let accounts = vec![(key, shared(0xDEADBEEF, vec![0xAB], owner, true))];
    let bytes = serialize_parameters(&ix, &accounts, &program_id).expect("valid inputs");

    // num_accounts = 1
    assert_eq!(&bytes[0..8], &1u64.to_le_bytes());
    // dup marker
    assert_eq!(bytes[8], 0xFF);
    // is_signer = 0, is_writable = 0, is_executable = 1
    assert_eq!(bytes[9], 0);
    assert_eq!(bytes[10], 0);
    assert_eq!(bytes[11], 1);
    // 4 bytes zero padding
    assert_eq!(&bytes[12..16], &[0u8; 4]);
    // 32B key, 32B owner
    assert_eq!(&bytes[16..48], &[1u8; 32]);
    assert_eq!(&bytes[48..80], &[2u8; 32]);
    // lamports
    assert_eq!(&bytes[80..88], &0xDEADBEEFu64.to_le_bytes());
    // data_len
    assert_eq!(&bytes[88..96], &1u64.to_le_bytes());
    // 1 byte of data
    assert_eq!(bytes[96], 0xAB);
    // align padding: 7 zero bytes (8 - 1 = 7)
    assert_eq!(&bytes[97..104], &[0u8; 7]);
    // 10240 zero bytes of realloc padding
    assert!(bytes[104..104 + 10240].iter().all(|&b| b == 0));
    // rent_epoch = u64::MAX
    let rent_off = 104 + 10240;
    assert_eq!(&bytes[rent_off..rent_off + 8], &u64::MAX.to_le_bytes());
    // instruction_data_len = 1
    let trailer_off = rent_off + 8;
    assert_eq!(&bytes[trailer_off..trailer_off + 8], &1u64.to_le_bytes());
    assert_eq!(bytes[trailer_off + 8], 0x10);
    // program_id = [7;32]
    assert_eq!(&bytes[trailer_off + 9..trailer_off + 9 + 32], &[7u8; 32]);
    // No trailing garbage.
    assert_eq!(bytes.len(), trailer_off + 9 + 32);
}
