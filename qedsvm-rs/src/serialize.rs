//! Account-buffer serialization conforming to `serialize_parameters_for_abiv1` (agave).
//! Produces the byte layout written at `MM_INPUT_START` (0x4_0000_0000) before BPF program invocation.
//! Non-dup account record: 0xFF, is_signer, is_writable, is_executable, u32 pad, [32] key, [32] owner,
//! u64 lamports, u64 data_len, [data], align_pad+MAX_PERMITTED_DATA_INCREASE zeros, u64 rent_epoch.
//! Dup: u8 original_index + 7B pad. Header: u64 num_accounts. Trailer: u64+[data] ix_data, [32] program_id.

use solana_account::{AccountSharedData, ReadableAccount};
use solana_instruction::{AccountMeta, Instruction};
use solana_program_entrypoint::{BPF_ALIGN_OF_U128, MAX_PERMITTED_DATA_INCREASE, NON_DUP_MARKER};
use solana_pubkey::Pubkey;

/// First-occurrence map over an instruction's `AccountMeta` list: `map[i] = Some(j)` iff
/// `metas[i].pubkey` first appears at index `j < i` (so `i` is a duplicate); `None` for
/// first occurrences. THE duplicate-account invariant: the serializer (dup-marker records),
/// the deserializer (dup-record skipping + first-occurrence write-back), and
/// `Svm::accounts_for_instruction` (positional pre/post alignment) all derive their dup
/// structure from this one function, so they cannot drift apart.
pub(crate) fn dup_map(metas: &[AccountMeta]) -> Vec<Option<usize>> {
    let mut first_seen: std::collections::HashMap<Pubkey, usize> =
        std::collections::HashMap::with_capacity(metas.len());
    metas
        .iter()
        .enumerate()
        .map(|(i, m)| match first_seen.entry(m.pubkey) {
            std::collections::hash_map::Entry::Occupied(e) => Some(*e.get()),
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(i);
                None
            }
        })
        .collect()
}

/// Errors from `serialize_parameters` — caller-input issues, not dynamic program failures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SerializeError {
    /// An `AccountMeta` references a pubkey absent from `accounts`.
    MissingAccount(Pubkey),
    /// Account count exceeds 255 (0xFF is reserved as `NON_DUP_MARKER`).
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

/// Serialize an instruction + accounts + program_id into the agave-conformant BPF input buffer.
/// Duplicate `AccountMeta`s (same pubkey) are compressed to the dup-marker form.
/// `rent_epoch` is hardcoded to `u64::MAX` (modern agave masks the real value).
pub fn serialize_parameters(
    instruction: &Instruction,
    accounts: &[(Pubkey, AccountSharedData)],
    program_id: &Pubkey,
) -> Result<Vec<u8>, SerializeError> {
    let n = instruction.accounts.len();
    if n > 255 {
        // 0xFF = NON_DUP_MARKER sentinel; 255 is the max valid index
        return Err(SerializeError::TooManyAccounts(n));
    }

    let mut buf = Vec::new();
    write_u64(&mut buf, n as u64);

    let seen = dup_map(&instruction.accounts); // first-occurrence index per slot, for dup detection

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
        buf.extend_from_slice(&[0u8; 4]); // u32 padding ("original_data_len")
        buf.extend_from_slice(meta.pubkey.as_ref()); // 32B key
        buf.extend_from_slice(account.owner().as_ref()); // 32B owner
        write_u64(&mut buf, account.lamports());
        let data = account.data();
        write_u64(&mut buf, data.len() as u64);
        buf.extend_from_slice(data);

        let align_pad = align_offset_to_bpf_u128(data.len());
        buf.extend(std::iter::repeat_n(
            0u8,
            align_pad + MAX_PERMITTED_DATA_INCREASE,
        ));

        write_u64(&mut buf, u64::MAX); // rent_epoch
    }

    // Trailer.
    write_u64(&mut buf, instruction.data.len() as u64);
    buf.extend_from_slice(&instruction.data);
    buf.extend_from_slice(program_id.as_ref());

    Ok(buf)
}

/// Look up an account by pubkey; linear scan is fine for typical account counts (≤ 64).
fn find_account(
    key: Pubkey,
    accounts: &[(Pubkey, AccountSharedData)],
) -> Option<&AccountSharedData> {
    accounts.iter().find(|(k, _)| *k == key).map(|(_, a)| a)
}

#[inline]
fn write_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

/// Padding bytes to align `data_len` to `BPF_ALIGN_OF_U128` (8). Equivalent to `(8 - data_len % 8) % 8`.
#[inline]
const fn align_offset_to_bpf_u128(data_len: usize) -> usize {
    let rem = data_len % BPF_ALIGN_OF_U128;
    if rem == 0 {
        0
    } else {
        BPF_ALIGN_OF_U128 - rem
    }
}
