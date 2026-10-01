//! Checked positions in aligned Solana input with non-duplicate accounts.
//! The lengths are supplied layout assumptions, not facts inferred from code.

pub struct InputOffsets {
    pub account_data: Vec<usize>,
    pub instruction_data: usize,
}

pub fn aligned_input_offsets(lengths: &[usize]) -> Result<InputOffsets, &'static str> {
    let mut cursor = 8usize;
    let mut account_data = Vec::with_capacity(lengths.len());
    for &len in lengths {
        account_data.push(cursor.checked_add(88).ok_or("account offset overflow")?);
        let padded = len
            .checked_add(10240)
            .and_then(|n| n.checked_add(7))
            .map(|n| n / 8 * 8)
            .ok_or("account size overflow")?;
        cursor = cursor
            .checked_add(96)
            .and_then(|n| n.checked_add(padded))
            .ok_or("input size overflow")?;
    }
    Ok(InputOffsets {
        account_data,
        instruction_data: cursor.checked_add(8).ok_or("instruction offset overflow")?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positions_include_alignment_growth_and_instruction_length() {
        for (lengths, accounts, instruction) in [
            (vec![], vec![], 16),
            (vec![41], vec![96], 10400),
            (vec![41, 8], vec![96, 10480], 20744),
        ] {
            let result = aligned_input_offsets(&lengths).unwrap();
            assert_eq!(result.account_data, accounts);
            assert_eq!(result.instruction_data, instruction);
        }
        assert!(aligned_input_offsets(&[usize::MAX]).is_err());
    }
}
