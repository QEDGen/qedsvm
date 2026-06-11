//! Probe the SIMD-0127 `sol_get_sysvar` syscall surface and dump every
//! result into accounts[0].data, so the diff harness can pin the model
//! against mollusk/agave byte-for-byte (soundness audit H7):
//!
//!   [0]        r0 of rent, offset 0, length 17 (expect 0)
//!   [1..18]    the rent bytes
//!   [18]       r0 of rent, offset 8, length 9 (slice path; expect 0)
//!   [19..28]   the slice bytes
//!   [28]       r0 of clock, offset 0, length 40 (expect 0)
//!   [29..69]   the clock bytes
//!   [69]       r0 of an UNKNOWN id (expect 2, SYSVAR_NOT_FOUND)
//!   [70]       r0 of rent, offset 0, length 18 (expect 1, OFFSET_LENGTH_EXCEEDS_SYSVAR)
//!   [71]       r0 of epoch_schedule, offset 0, length 33 (expect 0)
//!   [72..105]  the epoch_schedule bytes
//!   [105]      r0 of slot_hashes, offset 0, length 8 (expect 0)
//!   [106..114] the slot_hashes length prefix (512 entries LE)
//!
//! Account data must be ≥ 114 bytes.

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult, pubkey::Pubkey,
};

#[cfg(target_os = "solana")]
extern "C" {
    fn sol_get_sysvar(
        sysvar_id_addr: *const u8,
        var_addr: *mut u8,
        offset: u64,
        length: u64,
    ) -> u64;
}

#[cfg(not(target_os = "solana"))]
unsafe fn sol_get_sysvar(_: *const u8, _: *mut u8, _: u64, _: u64) -> u64 {
    unimplemented!()
}

const RENT_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2c, 0x5c, 0x51, 0x21, 0x8c, 0xc9, 0x4c, 0x3d, 0x4a, 0xf1,
    0x7f, 0x58, 0xda, 0xee, 0x08, 0x9b, 0xa1, 0xfd, 0x44, 0xe3, 0xdb, 0xd9, 0x8a, 0x00, 0x00,
    0x00, 0x00,
];
const CLOCK_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x18, 0xc7, 0x74, 0xc9, 0x28, 0x56, 0x63, 0x98, 0x69, 0x1d, 0x5e,
    0xb6, 0x8b, 0x5e, 0xb8, 0xa3, 0x9b, 0x4b, 0x6d, 0x5c, 0x73, 0x55, 0x5b, 0x21, 0x00, 0x00,
    0x00, 0x00,
];
const EPOCH_SCHEDULE_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x18, 0xdc, 0x3f, 0xee, 0x02, 0xd3, 0xe4, 0x7f, 0x01, 0x00, 0xf8,
    0xb0, 0x54, 0xf7, 0x94, 0x2e, 0x60, 0x59, 0x1e, 0x3f, 0x50, 0x87, 0x19, 0xa8, 0x05, 0x00,
    0x00, 0x00,
];
const SLOT_HASHES_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2f, 0x0a, 0xaf, 0xc6, 0xf2, 0x65, 0xe3, 0xfb, 0x77, 0xcc,
    0x7a, 0xda, 0x82, 0xc5, 0x29, 0xd0, 0xbe, 0x3b, 0x13, 0x6e, 0x2d, 0x00, 0x55, 0x20, 0x00,
    0x00, 0x00,
];
const UNKNOWN_ID: [u8; 32] = [0xAA; 32];

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    _instruction_data: &[u8],
) -> ProgramResult {
    let mut out = accounts[0].data.borrow_mut();
    let mut cursor = 0usize;

    let mut probe = |id: &[u8; 32], offset: u64, length: u64, out: &mut [u8], cursor: &mut usize| {
        let mut buf = [0u8; 64];
        let r0 = unsafe { sol_get_sysvar(id.as_ptr(), buf.as_mut_ptr(), offset, length) };
        out[*cursor] = r0 as u8;
        *cursor += 1;
        if r0 == 0 && length > 0 {
            let n = length as usize;
            out[*cursor..*cursor + n].copy_from_slice(&buf[..n]);
            *cursor += n;
        }
    };

    probe(&RENT_ID, 0, 17, &mut out, &mut cursor);
    probe(&RENT_ID, 8, 9, &mut out, &mut cursor);
    probe(&CLOCK_ID, 0, 40, &mut out, &mut cursor);
    probe(&UNKNOWN_ID, 0, 8, &mut out, &mut cursor);
    probe(&RENT_ID, 0, 18, &mut out, &mut cursor);
    probe(&EPOCH_SCHEDULE_ID, 0, 33, &mut out, &mut cursor);
    probe(&SLOT_HASHES_ID, 0, 8, &mut out, &mut cursor);

    Ok(())
}
