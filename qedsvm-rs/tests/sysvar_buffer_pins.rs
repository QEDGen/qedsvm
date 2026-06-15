//! H7: pin `SVM/Syscalls/SysvarData.lean` byte contents against mollusk default sysvars.
//! A mollusk/agave bump that changes a default or layout fails here before silently diverging the Lean model.
//! Run with: cargo test --features diff-mollusk --test sysvar_buffer_pins
#![cfg(feature = "diff-mollusk")]

use mollusk_svm::Mollusk;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Dump sysvar id + bincode buffer for re-deriving Lean constants; assertions below pin them.
#[test]
fn dump_sysvar_buffers() {
    let m = Mollusk::default();
    let s = &m.sysvars;

    let entries: Vec<(&str, [u8; 32], Vec<u8>)> = vec![
        ("clock", solana_sdk_ids::sysvar::clock::id().to_bytes(),
         bincode::serialize(&s.clock).unwrap()),
        ("epoch_schedule", solana_sdk_ids::sysvar::epoch_schedule::id().to_bytes(),
         bincode::serialize(&s.epoch_schedule).unwrap()),
        ("epoch_rewards", solana_sdk_ids::sysvar::epoch_rewards::id().to_bytes(),
         bincode::serialize(&s.epoch_rewards).unwrap()),
        ("rent", solana_sdk_ids::sysvar::rent::id().to_bytes(),
         bincode::serialize(&s.rent).unwrap()),
        ("slot_hashes", solana_sdk_ids::sysvar::slot_hashes::id().to_bytes(),
         bincode::serialize(&s.slot_hashes).unwrap()),
        ("stake_history", solana_sdk_ids::sysvar::stake_history::id().to_bytes(),
         bincode::serialize(&s.stake_history).unwrap()),
        ("last_restart_slot", solana_sdk_ids::sysvar::last_restart_slot::id().to_bytes(),
         bincode::serialize(&s.last_restart_slot).unwrap()),
    ];
    for (name, id, buf) in &entries {
        println!("{name}: id={} len={}", hex(id), buf.len());
        println!("{name}: buf={}", hex(buf));
    }
}

/// Pin exact buffers from `SysvarData.lean`; fails here in Rust on mollusk/agave bumps before Lean diverges.
#[test]
fn sysvar_buffers_match_lean_constants() {
    let m = Mollusk::default();
    let s = &m.sysvars;

    // clockBuf = zeros 40
    assert_eq!(bincode::serialize(&s.clock).unwrap(), vec![0u8; 40], "clockBuf");

    // epochScheduleBuf = 432_000 ×2 (u64 LE) + false + 16 zero bytes
    let mut epoch_schedule = Vec::new();
    epoch_schedule.extend_from_slice(&[0x80, 0x97, 0x06, 0, 0, 0, 0, 0]);
    epoch_schedule.extend_from_slice(&[0x80, 0x97, 0x06, 0, 0, 0, 0, 0]);
    epoch_schedule.push(0);
    epoch_schedule.extend_from_slice(&[0u8; 16]);
    assert_eq!(bincode::serialize(&s.epoch_schedule).unwrap(), epoch_schedule,
        "epochScheduleBuf");

    // epochRewardsBuf = zeros 81
    assert_eq!(bincode::serialize(&s.epoch_rewards).unwrap(), vec![0u8; 81],
        "epochRewardsBuf");

    // rentBuf = 3480 (u64 LE) + 2.0 (f64 LE) + 50
    let rent = vec![
        0x98, 0x0d, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0x40,
        0x32,
    ];
    assert_eq!(bincode::serialize(&s.rent).unwrap(), rent, "rentBuf");

    // slotHashesBuf = 8-byte LE length (512) + 512 × 40 zero bytes
    let mut slot_hashes = vec![0u8; 20488];
    slot_hashes[1] = 0x02;
    assert_eq!(bincode::serialize(&s.slot_hashes).unwrap(), slot_hashes,
        "slotHashesBuf");

    // stakeHistoryBuf = 8-byte LE length (1) + 32 zero bytes
    let mut stake_history = vec![0u8; 40];
    stake_history[0] = 0x01;
    assert_eq!(bincode::serialize(&s.stake_history).unwrap(), stake_history,
        "stakeHistoryBuf");

    // lastRestartSlotBuf = zeros 8
    assert_eq!(bincode::serialize(&s.last_restart_slot).unwrap(), vec![0u8; 8],
        "lastRestartSlotBuf");

    let pin_id = |name: &str, actual: [u8; 32], head: [u8; 8]| { // pin first 8 bytes of each sysvar id
        assert_eq!(&actual[..8], &head, "{name} id head");
    };
    pin_id("clock", solana_sdk_ids::sysvar::clock::id().to_bytes(),
        [0x06, 0xa7, 0xd5, 0x17, 0x18, 0xc7, 0x74, 0xc9]);
    pin_id("epoch_schedule", solana_sdk_ids::sysvar::epoch_schedule::id().to_bytes(),
        [0x06, 0xa7, 0xd5, 0x17, 0x18, 0xdc, 0x3f, 0xee]);
    pin_id("rent", solana_sdk_ids::sysvar::rent::id().to_bytes(),
        [0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2c, 0x5c, 0x51]);
    pin_id("slot_hashes", solana_sdk_ids::sysvar::slot_hashes::id().to_bytes(),
        [0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2f, 0x0a, 0xaf]);
    pin_id("stake_history", solana_sdk_ids::sysvar::stake_history::id().to_bytes(),
        [0x06, 0xa7, 0xd5, 0x17, 0x19, 0x35, 0x84, 0xd0]);
    pin_id("last_restart_slot", solana_sdk_ids::sysvar::last_restart_slot::id().to_bytes(),
        [0x06, 0xa7, 0xd5, 0x17, 0x19, 0x06, 0xdd, 0xe1]);
}
