//! Decode the wire format `SVM.Ffi.runElfBuffer` produces (see `Svm/Ffi.lean` for canonical layout):
//! `u8 status` (0=ELF fail, 1=executed); if 1: `u8 exit_kind` (0=OOB, 1=halted+u64, 2=faulted+u64),
//! `u64 cu_consumed`, `u32 input_len + [u8]`, `u32 num_logs + per-log u32+[u8]`, `u32 rd_len + [u8]`.

use std::fmt;

/// Outcome of a single program execution under the Lean VM.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExitOutcome {
    /// The CU budget was exhausted before the program halted.
    OutOfBudget,
    /// Program halted via a clean `exit`. NOTE (audit L1): any r0 is possible; `Faulted` is what
    /// distinguishes a real VM fault from a numerically identical program-returned exit code.
    Halted(u64),
    /// VM faulted (access violation, div-by-zero, etc. — Lean `State.vmError` channel).
    /// Payload is the legacy `ERR_*` sentinel; see M14 for the cross-engine mapping.
    Faulted(u64),
}

#[derive(Clone, Debug)]
pub struct RawResult {
    pub outcome: ExitOutcome,
    /// CU consumed. CPI callees share the parent's meter (see `Runner.executeFnCpiWithFuel`).
    pub compute_units_consumed: u64,
    /// Input region after execution; `deserialize_account_writes` slices it back into accounts.
    pub modified_input: Vec<u8>,
    pub logs: Vec<Vec<u8>>,
    pub return_data: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    /// `runElfBuffer` returned status=0: ELF decode failed in Lean.
    ElfDecodeFailed,
    /// Truncated or otherwise malformed wire bytes.
    Malformed(&'static str),
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeError::ElfDecodeFailed => write!(f, "ELF decode failed in Lean"),
            DecodeError::Malformed(why) => write!(f, "malformed Lean wire format: {why}"),
        }
    }
}

impl std::error::Error for DecodeError {}

/// Truncation error for every cursor read in this format.
const TRUNCATED: DecodeError = DecodeError::Malformed("buffer truncated");

pub fn decode(bytes: &[u8]) -> Result<RawResult, DecodeError> {
    let mut r = crate::cursor::ByteCursor::new(bytes);
    let status = r.u8().ok_or(TRUNCATED)?;
    match status {
        0 => Err(DecodeError::ElfDecodeFailed),
        1 => {
            let outcome = match r.u8().ok_or(TRUNCATED)? {
                0 => ExitOutcome::OutOfBudget,
                1 => ExitOutcome::Halted(r.u64().ok_or(TRUNCATED)?),
                2 => ExitOutcome::Faulted(r.u64().ok_or(TRUNCATED)?),
                _ => return Err(DecodeError::Malformed("unknown exit_kind")),
            };
            let compute_units_consumed = r.u64().ok_or(TRUNCATED)?;
            let input_len = r.u32().ok_or(TRUNCATED)? as usize;
            let modified_input = r.take(input_len).ok_or(TRUNCATED)?.to_vec();
            let num_logs = r.u32().ok_or(TRUNCATED)? as usize;
            let mut logs = Vec::with_capacity(num_logs);
            for _ in 0..num_logs {
                let n = r.u32().ok_or(TRUNCATED)? as usize;
                logs.push(r.take(n).ok_or(TRUNCATED)?.to_vec());
            }
            let rd_len = r.u32().ok_or(TRUNCATED)? as usize;
            let return_data = r.take(rd_len).ok_or(TRUNCATED)?.to_vec();
            Ok(RawResult {
                outcome,
                compute_units_consumed,
                modified_input,
                logs,
                return_data,
            })
        }
        _ => Err(DecodeError::Malformed("unknown status byte")),
    }
}
