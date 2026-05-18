//! Account-buffer serialization, agave-conformant.
//!
//! Produces the byte layout that real Solana programs deserialize via
//! `solana_program_entrypoint::deserialize` (the BPF program-side
//! entry point macro). This is the byte sequence written at
//! `MM_INPUT_START` (= 0x4_0000_0000) before a program is invoked.
//!
//! Cross-referenced against agave master:
//!   - `program-runtime/src/serialization.rs::serialize_parameters_for_abiv1`
//!     (host-side serializer, the "what we emulate")
//!   - `sdk/program-entrypoint/src/lib.rs::deserialize`
//!     (program-side deserializer, our round-trip oracle in tests)
//!
//! Constants exposed by `solana-program-entrypoint`:
//!   - `MAX_PERMITTED_DATA_INCREASE = 10240`
//!   - `BPF_ALIGN_OF_U128 = 8`  (the BPF target's align_of::<u128>())
//!   - `NON_DUP_MARKER = 0xFF`
//!
//! Layout per non-duplicate account:
//!   u8  0xFF (NON_DUP_MARKER)
//!   u8  is_signer
//!   u8  is_writable
//!   u8  is_executable
//!   u32 padding (zeros; program-side patches this in-place with
//!                data_len during deserialize as `original_data_len`)
//!   [32] key
//!   [32] owner
//!   u64 lamports (LE)
//!   u64 data_len (LE)
//!   [data_len] data
//!   [(8 - data_len % 8) % 8] zero padding   ┐ together: realloc room
//!   [MAX_PERMITTED_DATA_INCREASE] zero      ┘  ends 8-aligned
//!   u64 rent_epoch (LE, u64::MAX in modern releases)
//!
//! Per duplicate account:
//!   u8  position (index of original)
//!   [7] zero padding (→ 8-byte alignment)
//!
//! Header / trailer:
//!   u64 num_accounts (LE)               ┐ before account list
//!   ...accounts...
//!   u64 instruction_data_len (LE)       ┐ after account list
//!   [instruction_data_len] instruction_data
//!   [32] program_id

use solana_account::{AccountSharedData, ReadableAccount};
use solana_instruction::Instruction;
use solana_program_entrypoint::{
    BPF_ALIGN_OF_U128, MAX_PERMITTED_DATA_INCREASE, NON_DUP_MARKER,
};
use solana_pubkey::Pubkey;

/// Errors `serialize_parameters` can surface. These are all
/// caller-input issues — programmer errors at the harness level, not
/// dynamic failures inside the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SerializeError {
    /// An `AccountMeta` in `instruction.accounts` references a
    /// pubkey that doesn't appear in the supplied `accounts` list.
    MissingAccount(Pubkey),
    /// `instruction.accounts` exceeds the protocol cap (256 — the
    /// dup marker is a `u8`, and 0xFF is `NON_DUP_MARKER`, so the
    /// addressable range is 0..=254 first occurrences).
    TooManyAccounts(usize),
}

impl std::fmt::Display for SerializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingAccount(pk) => write!(
                f,
                "instruction references pubkey {pk} that is not in the supplied accounts list",
            ),
            Self::TooManyAccounts(n) => write!(
                f,
                "instruction has {n} accounts; protocol cap is 255 (NON_DUP_MARKER reserves 0xFF)",
            ),
        }
    }
}

impl std::error::Error for SerializeError {}

/// Serialize an instruction + its accounts + program_id into the
/// agave-conformant input buffer for BPF program invocation.
///
/// `accounts` are looked up by pubkey from `instruction.accounts`'s
/// `AccountMeta` entries. The order of accounts in the resulting
/// buffer matches `instruction.accounts` (which is what programs see).
/// Duplicate `AccountMeta`s (same pubkey appearing more than once in
/// the instruction's metadata) are compressed to the dup-marker form.
///
/// `rent_epoch` is hardcoded to `u64::MAX` to match modern agave; the
/// runtime has been masking out the real value for several releases.
pub fn serialize_parameters(
    instruction: &Instruction,
    accounts: &[(Pubkey, AccountSharedData)],
    program_id: &Pubkey,
) -> Result<Vec<u8>, SerializeError> {
    let n = instruction.accounts.len();
    // 255 is the largest valid first-occurrence index; 0xFF is the
    // dup-marker sentinel and would collide.
    if n > 255 {
        return Err(SerializeError::TooManyAccounts(n));
    }

    let mut buf = Vec::new();
    write_u64(&mut buf, n as u64);

    // First-occurrence index, for dup detection.
    let mut seen: Vec<Option<usize>> = vec![None; n];
    for (i, meta) in instruction.accounts.iter().enumerate() {
        let first = (0..i).find(|j| instruction.accounts[*j].pubkey == meta.pubkey);
        if let Some(j) = first {
            seen[i] = Some(j);
        }
    }

    for (i, meta) in instruction.accounts.iter().enumerate() {
        if let Some(j) = seen[i] {
            buf.push(j as u8);
            buf.extend_from_slice(&[0u8; 7]);
            continue;
        }
        let account = find_account(meta.pubkey, accounts)
            .ok_or(SerializeError::MissingAccount(meta.pubkey))?;

        buf.push(NON_DUP_MARKER);
        buf.push(meta.is_signer as u8);
        buf.push(meta.is_writable as u8);
        buf.push(account.executable() as u8);
        buf.extend_from_slice(&[0u8; 4]);                   // u32 padding ("original_data_len")
        buf.extend_from_slice(meta.pubkey.as_ref());        // 32B key
        buf.extend_from_slice(account.owner().as_ref());    // 32B owner
        write_u64(&mut buf, account.lamports());
        let data = account.data();
        write_u64(&mut buf, data.len() as u64);
        buf.extend_from_slice(data);

        let align_pad = align_offset_to_bpf_u128(data.len());
        buf.extend(std::iter::repeat_n(0u8, align_pad + MAX_PERMITTED_DATA_INCREASE));

        write_u64(&mut buf, u64::MAX);                      // rent_epoch
    }

    // Trailer.
    write_u64(&mut buf, instruction.data.len() as u64);
    buf.extend_from_slice(&instruction.data);
    buf.extend_from_slice(program_id.as_ref());

    Ok(buf)
}

/// Look up an account by pubkey. Linear scan — fine for the typical
/// instruction account counts (≤ 64).
fn find_account<'a>(
    key: Pubkey,
    accounts: &'a [(Pubkey, AccountSharedData)],
) -> Option<&'a AccountSharedData> {
    accounts.iter().find(|(k, _)| *k == key).map(|(_, a)| a)
}

#[inline]
fn write_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

/// Bytes to add after `data_len` to reach a `BPF_ALIGN_OF_U128`
/// (=8) boundary. Matches `(data_len as *const u8).align_offset(8)`
/// from agave's serializer — since `align_offset` on raw bytes is
/// equivalent to `(8 - data_len % 8) % 8`.
#[inline]
const fn align_offset_to_bpf_u128(data_len: usize) -> usize {
    let rem = data_len % BPF_ALIGN_OF_U128;
    if rem == 0 { 0 } else { BPF_ALIGN_OF_U128 - rem }
}
