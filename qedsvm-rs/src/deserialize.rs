//! Parse the post-execution input buffer into modified accounts (inverse of `serialize_parameters`).
//! One `(Pubkey, AccountSharedData)` per `AccountMeta`; duplicates map to the first-occurrence record.

use solana_account::AccountSharedData;
use solana_account::WritableAccount;
use solana_instruction::Instruction;
use solana_program_entrypoint::MAX_PERMITTED_DATA_INCREASE;
use solana_pubkey::Pubkey;

/// Walk `buffer` (post-execution `INPUT_START` region), overwriting each non-dup account's
/// lamports/owner/data from `buffer`; executable and rent_epoch inherited from `pre_accounts`.
/// Returns `Err` on malformed buffer.
pub fn deserialize_account_writes(
    buffer: &[u8],
    instruction: &Instruction,
    pre_accounts: &[(Pubkey, AccountSharedData)],
) -> Result<Vec<(Pubkey, AccountSharedData)>, DeserializeError> {
    let mut r = Reader::new(buffer);

    let num_accounts = r.read_u64()? as usize;
    if num_accounts != instruction.accounts.len() {
        return Err(DeserializeError::AccountCountMismatch {
            expected: instruction.accounts.len(),
            got: num_accounts,
        });
    }

    // Walk the buffer once, collecting per-first-occurrence updates.
    // We do NOT read `dup_info` from the buffer: Pinocchio's borrow-tracking (`solana-account-view`)
    // overlays `borrow_state` on that byte and can leave any 0..=255 value there (issue #2).
    // Dup structure is fully determined by `instruction.accounts` — same as the serializer — so
    // we recompute it from there and skip 8 bytes for each detected dup.
    let mut by_first_occurrence: Vec<Option<AccountSharedData>> = vec![None; num_accounts];
    for (i, slot) in by_first_occurrence.iter_mut().enumerate() {
        let first = (0..i).find(|j| instruction.accounts[*j].pubkey == instruction.accounts[i].pubkey);
        if first.is_some() {
            // Dup: 1B (post-execution borrow_state, ignored) + 7B padding.
            r.skip(8)?;
        } else {
            // Non-dup: 1B (post-execution borrow_state, ignored) + rest of record.
            r.skip(1)?;
            let updated = parse_non_dup_record(&mut r, &instruction.accounts[i].pubkey, pre_accounts)?;
            *slot = Some(updated);
        }
    }

    // Trailer: instruction_data_len + instruction_data + program_id — parse to validate buffer structure.
    let ix_data_len = r.read_u64()? as usize;
    r.skip(ix_data_len)?;
    r.skip(32)?;  // program_id

    let mut result = Vec::with_capacity(num_accounts);
    for (i, meta) in instruction.accounts.iter().enumerate() {
        let first = (0..=i)
            .find(|j| instruction.accounts[*j].pubkey == meta.pubkey)
            .unwrap();  // at minimum, i itself
        let updated = by_first_occurrence[first]
            .clone()
            .ok_or(DeserializeError::MissingFirstOccurrence(first))?;
        result.push((meta.pubkey, updated));
    }
    Ok(result)
}

fn parse_non_dup_record(
    r: &mut Reader<'_>,
    meta_key: &Pubkey,
    pre_accounts: &[(Pubkey, AccountSharedData)],
) -> Result<AccountSharedData, DeserializeError> {
    // 1B is_signer + 1B is_writable + 1B is_executable + 4B padding — all runtime-only, skip.
    r.skip(7)?;
    let mut key_bytes = [0u8; 32];
    r.read_into(&mut key_bytes)?;
    let key = Pubkey::from(key_bytes);
    if &key != meta_key {
        return Err(DeserializeError::PubkeyMismatch { expected: *meta_key, got: key });
    }
    let mut owner_bytes = [0u8; 32];
    r.read_into(&mut owner_bytes)?;
    let owner = Pubkey::from(owner_bytes);
    let lamports = r.read_u64()?;
    let data_len = r.read_u64()? as usize;
    if data_len > MAX_PERMITTED_DATA_INCREASE + pre_accounts
        .iter()
        .find(|(k, _)| *k == *meta_key)
        .map(|(_, a)| {
            use solana_account::ReadableAccount;
            a.data().len()
        })
        .unwrap_or(0)
    {
        return Err(DeserializeError::DataLengthOverflow(data_len));
    }
    let data = r.read_bytes(data_len)?.to_vec();
    // Skip the reserved realloc-room: pre_data_len + pre_align + MAX_PERMITTED_DATA_INCREASE
    // bytes total; remaining = pre_data_len + pre_align - post_data_len - post_align + 10240.
    let pre_data_len = pre_accounts
        .iter()
        .find(|(k, _)| *k == *meta_key)
        .map(|(_, a)| a.data().len())
        .unwrap_or(0);
    let pre_align_pad = (8 - pre_data_len % 8) % 8;
    let post_align_pad = (8 - data_len % 8) % 8;
    let remaining_pad = pre_data_len + pre_align_pad
        + MAX_PERMITTED_DATA_INCREASE
        - data_len - post_align_pad;
    r.skip(post_align_pad + remaining_pad)?;
    r.skip(8)?;  // rent_epoch

    // `executable` and `rent_epoch` are always inherited from pre-state (immutable to programs).
    // Load-bearing: `validate_post_state` does not re-check these fields.
    let pre = pre_accounts
        .iter()
        .find(|(k, _)| *k == *meta_key)
        .ok_or(DeserializeError::UnknownPubkeyInInstruction(*meta_key))?
        .1
        .clone();
    use solana_account::ReadableAccount;
    let mut out = AccountSharedData::new(lamports, data.len(), &owner);
    out.set_data_from_slice(&data);
    out.set_executable(pre.executable());
    out.set_rent_epoch(pre.rent_epoch());
    Ok(out)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeserializeError {
    Truncated,
    AccountCountMismatch { expected: usize, got: usize },
    MissingFirstOccurrence(usize),
    PubkeyMismatch { expected: Pubkey, got: Pubkey },
    DataLengthOverflow(usize),
    UnknownPubkeyInInstruction(Pubkey),
}

impl std::fmt::Display for DeserializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated => write!(f, "buffer truncated"),
            Self::AccountCountMismatch { expected, got } =>
                write!(f, "account count mismatch: expected {expected}, got {got}"),
            Self::MissingFirstOccurrence(i) =>
                write!(f, "missing first-occurrence record for account {i}"),
            Self::PubkeyMismatch { expected, got } =>
                write!(f, "pubkey mismatch: expected {expected}, got {got}"),
            Self::DataLengthOverflow(n) =>
                write!(f, "data_len {n} exceeds pre-state + MAX_PERMITTED_DATA_INCREASE"),
            Self::UnknownPubkeyInInstruction(pk) =>
                write!(f, "instruction references unknown pubkey {pk}"),
        }
    }
}

impl std::error::Error for DeserializeError {}

struct Reader<'a> { buf: &'a [u8], pos: usize }

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Self { Self { buf, pos: 0 } }

    fn take(&mut self, n: usize) -> Result<&'a [u8], DeserializeError> {
        if self.pos + n > self.buf.len() { return Err(DeserializeError::Truncated) }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }

    fn skip(&mut self, n: usize) -> Result<(), DeserializeError> { self.take(n)?; Ok(()) }
    fn read_u64(&mut self) -> Result<u64, DeserializeError> {
        let b = self.take(8)?;
        Ok(u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))
    }
    fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], DeserializeError> { self.take(n) }
    fn read_into(&mut self, dst: &mut [u8]) -> Result<(), DeserializeError> {
        let s = self.take(dst.len())?;
        dst.copy_from_slice(s);
        Ok(())
    }
}
