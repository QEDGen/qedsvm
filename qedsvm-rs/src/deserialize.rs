//! Parse the post-execution input buffer into modified accounts (inverse of `serialize_parameters`).
//! One `(Pubkey, AccountSharedData)` per `AccountMeta`; duplicates map to the first-occurrence record.

use crate::cursor::ByteCursor;
use solana_account::AccountSharedData;
use solana_account::WritableAccount;
use solana_instruction::Instruction;
use solana_program_entrypoint::MAX_PERMITTED_DATA_INCREASE;
use solana_pubkey::Pubkey;

/// Each instruction reference's account, and beside them its raw `data_len` field.
pub(crate) type AccountWrites = (Vec<(Pubkey, AccountSharedData)>, Vec<u64>);

/// Walk `buffer` (post-execution `INPUT_START` region), overwriting each non-dup account's
/// lamports/owner/data from `buffer`; executable and rent_epoch inherited from `pre_accounts`.
/// Returns `Err` on malformed buffer, or if a program set a length the runtime would reject.
pub fn deserialize_account_writes(
    buffer: &[u8],
    instruction: &Instruction,
    pre_accounts: &[(Pubkey, AccountSharedData)],
) -> Result<Vec<(Pubkey, AccountSharedData)>, DeserializeError> {
    let (accounts, raw_lens) = read_account_writes(buffer, instruction, pre_accounts)?;
    for ((_, account), raw) in accounts.iter().zip(&raw_lens) {
        use solana_account::ReadableAccount;
        if *raw != account.data().len() as u64 {
            return Err(DeserializeError::DataLengthOverflow(*raw as usize));
        }
    }
    Ok(accounts)
}

/// As [`deserialize_account_writes`], but a program's oversized length field is a value the
/// account-change check must judge, not a parse failure. Returns each reference's raw length
/// field beside its account; the account holds only the bytes the buffer has room for.
pub(crate) fn read_account_writes(
    buffer: &[u8],
    instruction: &Instruction,
    pre_accounts: &[(Pubkey, AccountSharedData)],
) -> Result<AccountWrites, DeserializeError> {
    let mut r = ByteCursor::new(buffer);

    let num_accounts = r.u64().ok_or(DeserializeError::Truncated)? as usize;
    if num_accounts != instruction.accounts.len() {
        return Err(DeserializeError::AccountCountMismatch {
            expected: instruction.accounts.len(),
            got: num_accounts,
        });
    }

    // Walk the buffer once, collecting per-first-occurrence updates.
    // We do NOT read `dup_info` from the buffer: Pinocchio's borrow-tracking (`solana-account-view`)
    // overlays `borrow_state` on that byte and can leave any 0..=255 value there (issue #2).
    // Dup structure is fully determined by `instruction.accounts` — the shared `dup_map`
    // invariant the serializer also uses — so we recompute it and skip 8 bytes per dup.
    let dup_of = crate::serialize::dup_map(&instruction.accounts);
    let mut by_first_occurrence: Vec<Option<(AccountSharedData, u64)>> = vec![None; num_accounts];
    for (i, slot) in by_first_occurrence.iter_mut().enumerate() {
        if dup_of[i].is_some() {
            // Dup: 1B (post-execution borrow_state, ignored) + 7B padding.
            r.skip(8).ok_or(DeserializeError::Truncated)?;
        } else {
            // Non-dup: 1B (post-execution borrow_state, ignored) + rest of record.
            r.skip(1).ok_or(DeserializeError::Truncated)?;
            let updated =
                parse_non_dup_record(&mut r, &instruction.accounts[i].pubkey, pre_accounts)?;
            *slot = Some(updated);
        }
    }

    // Trailer: instruction_data_len + instruction_data + program_id — parse to validate buffer structure.
    let ix_data_len = r.u64().ok_or(DeserializeError::Truncated)? as usize;
    r.skip(ix_data_len).ok_or(DeserializeError::Truncated)?;
    r.skip(32).ok_or(DeserializeError::Truncated)?; // program_id

    let mut result = Vec::with_capacity(num_accounts);
    let mut raw_lens = Vec::with_capacity(num_accounts);
    for (i, meta) in instruction.accounts.iter().enumerate() {
        let first = dup_of[i].unwrap_or(i); // first occurrence of this pubkey (i itself if non-dup)
        let (updated, raw_len) = by_first_occurrence[first]
            .clone()
            .ok_or(DeserializeError::MissingFirstOccurrence(first))?;
        result.push((meta.pubkey, updated));
        raw_lens.push(raw_len);
    }
    Ok((result, raw_lens))
}

fn parse_non_dup_record(
    r: &mut ByteCursor<'_>,
    meta_key: &Pubkey,
    pre_accounts: &[(Pubkey, AccountSharedData)],
) -> Result<(AccountSharedData, u64), DeserializeError> {
    use solana_account::ReadableAccount;
    // 1B is_signer + 1B is_writable + 1B is_executable + 4B padding + 32B key: agave reads none
    // of these back, so a program's writes to them have no effect.
    r.skip(7 + 32).ok_or(DeserializeError::Truncated)?;
    let mut owner_bytes = [0u8; 32];
    r.read_into(&mut owner_bytes)
        .ok_or(DeserializeError::Truncated)?;
    let owner = Pubkey::from(owner_bytes);
    let lamports = r.u64().ok_or(DeserializeError::Truncated)?;
    let raw_len = r.u64().ok_or(DeserializeError::Truncated)?;
    let pre = &pre_accounts
        .iter()
        .find(|(k, _)| *k == *meta_key)
        .ok_or(DeserializeError::UnknownPubkeyInInstruction(*meta_key))?
        .1;
    let pre_data_len = pre.data().len();
    let room = pre_data_len + MAX_PERMITTED_DATA_INCREASE;
    let data_len = usize::try_from(raw_len).map_or(room, |n| n.min(room));
    let data = r
        .take(data_len)
        .ok_or(DeserializeError::Truncated)?
        .to_vec();
    // The record's data area is fixed by the pre-state length, whatever the program set.
    let pre_align_pad = (8 - pre_data_len % 8) % 8;
    r.skip(room + pre_align_pad - data_len)
        .ok_or(DeserializeError::Truncated)?;
    r.skip(8).ok_or(DeserializeError::Truncated)?; // rent_epoch

    // `executable` and `rent_epoch` are always inherited from pre-state (immutable to programs).
    let mut out = AccountSharedData::new(lamports, data.len(), &owner);
    out.set_data_from_slice(&data);
    out.set_executable(pre.executable());
    out.set_rent_epoch(pre.rent_epoch());
    Ok((out, raw_len))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeserializeError {
    Truncated,
    AccountCountMismatch { expected: usize, got: usize },
    MissingFirstOccurrence(usize),
    DataLengthOverflow(usize),
    UnknownPubkeyInInstruction(Pubkey),
}

impl std::fmt::Display for DeserializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated => write!(f, "buffer truncated"),
            Self::AccountCountMismatch { expected, got } => {
                write!(f, "account count mismatch: expected {expected}, got {got}")
            }
            Self::MissingFirstOccurrence(i) => {
                write!(f, "missing first-occurrence record for account {i}")
            }
            Self::DataLengthOverflow(n) => write!(
                f,
                "data_len {n} exceeds pre-state + MAX_PERMITTED_DATA_INCREASE"
            ),
            Self::UnknownPubkeyInInstruction(pk) => {
                write!(f, "instruction references unknown pubkey {pk}")
            }
        }
    }
}

impl std::error::Error for DeserializeError {}
