//! Parse the post-execution input buffer back into modified accounts.
//!
//! Inverse of `serialize::serialize_parameters`. After the program
//! halts, the input region holds the same layout it had at entry,
//! except that the program may have written to:
//!   - the `lamports` slot (offset 64 within an account record)
//!   - the `owner` slot (offset 32 within an account record)
//!   - the `data` bytes
//!
//! Modern releases also let programs grow `data` up to
//! `MAX_PERMITTED_DATA_INCREASE` extra bytes by writing the new length
//! into the `data_len` slot. We honor that.
//!
//! Each entry in `instruction.accounts` produces one
//! `(Pubkey, AccountSharedData)` in the output, matching Mollusk's
//! `resulting_accounts` convention. Duplicate `AccountMeta`s map to
//! the same first-occurrence record (they share buffer memory).

use solana_account::AccountSharedData;
use solana_account::WritableAccount;
use solana_instruction::Instruction;
use solana_program_entrypoint::{MAX_PERMITTED_DATA_INCREASE, NON_DUP_MARKER};
use solana_pubkey::Pubkey;

/// Walk `buffer` (the post-execution `INPUT_START` region) and produce
/// one `(Pubkey, AccountSharedData)` per `AccountMeta` in `instruction`.
///
/// `pre_accounts` is the set of accounts the user passed in. Each
/// non-duplicate account's lamports / owner / data are overwritten
/// with whatever lives in `buffer`; everything else (rent_epoch, the
/// account's *executable* bit, the *owner* on read-only accounts —
/// real agave allows owner mutation only on writable owned accounts
/// but we don't enforce that here) is inherited from the pre-state.
///
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
    // Subsequent dup entries share that update.
    let mut by_first_occurrence: Vec<Option<AccountSharedData>> = vec![None; num_accounts];

    for i in 0..num_accounts {
        let dup_info = r.read_u8()?;
        if dup_info == NON_DUP_MARKER {
            let updated = parse_non_dup_record(&mut r, &instruction.accounts[i].pubkey, pre_accounts)?;
            by_first_occurrence[i] = Some(updated);
        } else {
            // 7 bytes padding, then this entry inherits from
            // `by_first_occurrence[dup_info as usize]`.
            r.skip(7)?;
            let src = dup_info as usize;
            if src >= num_accounts || by_first_occurrence[src].is_none() {
                return Err(DeserializeError::InvalidDupIndex(src));
            }
        }
    }

    // Trailer: instruction_data_len + instruction_data + program_id.
    // We don't care about these (we already have them from `instruction`),
    // but parse them anyway to validate the buffer's structure.
    let ix_data_len = r.read_u64()? as usize;
    r.skip(ix_data_len)?;
    r.skip(32)?;  // program_id

    // Build the result list: one entry per AccountMeta, in order,
    // looking up the first-occurrence update.
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
    // 1B is_signer + 1B is_writable + 1B is_executable + 4B padding —
    // none of these are modifiable from inside the program (executable
    // becomes immutable once set; signer/writable are runtime-only
    // flags). Skip 'em.
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
    // Skip alignment padding + realloc reserve + rent_epoch.
    let align_pad = (8 - data_len % 8) % 8;
    r.skip(align_pad + MAX_PERMITTED_DATA_INCREASE)?;
    r.skip(8)?;  // rent_epoch

    // Build the post-execution account. We inherit `executable` and
    // `rent_epoch` from the pre-state since the program can't change
    // them — sticking with what the user supplied.
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
    InvalidDupIndex(usize),
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
            Self::InvalidDupIndex(i) =>
                write!(f, "dup_info points at non-existent first-occurrence index {i}"),
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
    fn read_u8(&mut self) -> Result<u8, DeserializeError> { Ok(self.take(1)?[0]) }
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
