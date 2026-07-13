use solana_sbpf::ebpf;

use crate::diagnostic::{DiagnosticKind, LiftError};

/// Cursor over a concrete logical-PC trace. All trace indexing and advancement
/// lives here so the walker cannot accidentally mix a PC with the wrong index.
pub(super) struct TraceCursor<'a> {
    pcs: &'a [usize],
    index: usize,
}

impl<'a> TraceCursor<'a> {
    pub(super) fn new(pcs: &'a [usize]) -> Result<Self, LiftError> {
        if pcs.is_empty() {
            return Err(LiftError::new(
                DiagnosticKind::TraceInput,
                "qedlift: trace must contain at least one logical PC",
            ));
        }
        Ok(Self { pcs, index: 0 })
    }

    pub(super) fn current(&self) -> Option<usize> {
        self.pcs.get(self.index).copied()
    }

    pub(super) fn next(&self) -> Option<usize> {
        self.pcs.get(self.index + 1).copied()
    }

    pub(super) fn advance(&mut self) {
        self.index += 1;
    }

    pub(super) fn contains(&self, pc: usize) -> bool {
        self.pcs.contains(&pc)
    }

    pub(super) fn walk_cap(&self) -> usize {
        self.pcs.len() + 8
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BranchDecision {
    NotConditional,
    Taken,
    FallThrough,
}

impl BranchDecision {
    pub(super) const fn as_option(self) -> Option<bool> {
        match self {
            Self::NotConditional => None,
            Self::Taken => Some(true),
            Self::FallThrough => Some(false),
        }
    }

    pub(super) const fn is_taken(self) -> bool {
        matches!(self, Self::Taken)
    }
}

pub(super) fn is_cond_jump_opc(opc: u8) -> bool {
    matches!(
        opc,
        ebpf::JEQ64_IMM
            | ebpf::JEQ32_IMM
            | ebpf::JNE64_IMM
            | ebpf::JNE32_IMM
            | ebpf::JGT64_IMM
            | ebpf::JGT32_IMM
            | ebpf::JSGT64_IMM
            | ebpf::JSGT32_IMM
            | ebpf::JSLE64_IMM
            | ebpf::JSLE32_IMM
            | ebpf::JLT64_IMM
            | ebpf::JLT32_IMM
            | ebpf::JLE64_IMM
            | ebpf::JLE32_IMM
            | ebpf::JSLT64_IMM
            | ebpf::JSLT32_IMM
            | ebpf::JGE64_IMM
            | ebpf::JGE32_IMM
            | ebpf::JSGE64_IMM
            | ebpf::JSGE32_IMM
            | ebpf::JSET64_IMM
            | ebpf::JSET32_IMM
            | ebpf::JEQ64_REG
            | ebpf::JEQ32_REG
            | ebpf::JNE64_REG
            | ebpf::JNE32_REG
            | ebpf::JLT64_REG
            | ebpf::JLT32_REG
            | ebpf::JSLE64_REG
            | ebpf::JSLE32_REG
            | ebpf::JGT64_REG
            | ebpf::JGT32_REG
            | ebpf::JLE64_REG
            | ebpf::JLE32_REG
            | ebpf::JSGE64_REG
            | ebpf::JSGE32_REG
            | ebpf::JGE64_REG
            | ebpf::JGE32_REG
            | ebpf::JSGT64_REG
            | ebpf::JSGT32_REG
            | ebpf::JSLT64_REG
            | ebpf::JSLT32_REG
            | ebpf::JSET64_REG
            | ebpf::JSET32_REG
    )
}

/// Whether the conditional jump at `pc_iter` is taken.
/// Trace: taken iff next PC ≠ pc+1; target mismatch vs decoded offset = fail-closed.
/// Static: discriminator-driven where possible, else fall-through.
pub(super) fn resolve_branch_taken(
    trace: Option<&TraceCursor<'_>>,
    pc_iter: usize,
    ins: &ebpf::Insn,
    jtgt: i64,
    is_cond_jump: bool,
    target_disc: Option<i64>,
) -> Result<BranchDecision, LiftError> {
    let branch_taken = if let Some(cursor) = trace {
        if is_cond_jump {
            let next = cursor.next();
            let taken = next != Some(pc_iter + 1);
            if taken {
                if let Some(n) = next {
                    if n as i64 != jtgt {
                        return Err(LiftError::new(
                            DiagnosticKind::TraceInput,
                            format!(
                                "trace/decoder mismatch at pc {}: trace goes to {} \
                             but the decoded jump target is {} (off={})",
                                pc_iter, n, jtgt, ins.off
                            ),
                        ));
                    }
                }
            }
            if taken {
                BranchDecision::Taken
            } else {
                BranchDecision::FallThrough
            }
        } else {
            BranchDecision::NotConditional
        }
    } else {
        match (ins.opc, target_disc) {
            (ebpf::JEQ64_IMM, Some(td)) | (ebpf::JEQ32_IMM, Some(td)) if ins.imm == td => {
                BranchDecision::Taken
            }
            (ebpf::JNE64_IMM, Some(td)) | (ebpf::JNE32_IMM, Some(td)) if ins.imm != td => {
                BranchDecision::Taken
            }
            // JGT: take branch when td > imm (disc > N → upper_half pattern).
            (ebpf::JGT64_IMM, Some(td)) | (ebpf::JGT32_IMM, Some(td)) if td > ins.imm => {
                BranchDecision::Taken
            }
            _ if is_cond_jump => BranchDecision::FallThrough,
            _ => BranchDecision::NotConditional,
        }
    };
    Ok(branch_taken)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Expr;
    use crate::exec::syscall_registry::{classify_call_imm, CallImmClassification};
    use crate::exec::walk::{
        exit_disposition, merge_blob_splits, merge_hot_regions, ExitDisposition,
    };
    use crate::state::SymState;

    fn insn(opc: u8, off: i16, imm: i64) -> ebpf::Insn {
        ebpf::Insn {
            ptr: 0,
            opc,
            dst: 0,
            src: 0,
            off,
            imm,
        }
    }

    #[test]
    fn trace_cursor_types_empty_and_exhausted_traces() {
        let error = TraceCursor::new(&[]).err().expect("empty trace must fail");
        assert_eq!(error.kind(), DiagnosticKind::TraceInput);

        let mut cursor = TraceCursor::new(&[4]).expect("one-PC trace");
        assert_eq!(cursor.current(), Some(4));
        assert_eq!(cursor.next(), None);
        cursor.advance();
        assert_eq!(cursor.current(), None);
    }

    #[test]
    fn static_discriminator_decides_jeq_jne_and_jgt() {
        for (opc, imm, discriminator, expected) in [
            (ebpf::JEQ64_IMM, 7, 7, BranchDecision::Taken),
            (ebpf::JEQ64_IMM, 7, 8, BranchDecision::FallThrough),
            (ebpf::JNE64_IMM, 7, 8, BranchDecision::Taken),
            (ebpf::JNE64_IMM, 7, 7, BranchDecision::FallThrough),
            (ebpf::JGT64_IMM, 7, 8, BranchDecision::Taken),
            (ebpf::JGT64_IMM, 7, 7, BranchDecision::FallThrough),
        ] {
            let instruction = insn(opc, 2, imm);
            let decision =
                resolve_branch_taken(None, 4, &instruction, 7, true, Some(discriminator))
                    .expect("static branch decision");
            assert_eq!(decision, expected);
        }
    }

    #[test]
    fn trace_decides_taken_and_fallthrough_branches() {
        let instruction = insn(ebpf::JEQ64_IMM, 2, 7);
        let fallthrough_trace = TraceCursor::new(&[4, 5]).expect("trace cursor");
        let taken_trace = TraceCursor::new(&[4, 7]).expect("trace cursor");
        let fallthrough =
            resolve_branch_taken(Some(&fallthrough_trace), 4, &instruction, 7, true, None)
                .expect("fall-through decision");
        let taken = resolve_branch_taken(Some(&taken_trace), 4, &instruction, 7, true, None)
            .expect("taken decision");

        assert_eq!(fallthrough, BranchDecision::FallThrough);
        assert_eq!(taken, BranchDecision::Taken);
    }

    #[test]
    fn trace_target_mismatch_is_a_typed_input_error() {
        let instruction = insn(ebpf::JEQ64_IMM, 2, 7);
        let trace = TraceCursor::new(&[4, 9]).expect("trace cursor");
        let error = resolve_branch_taken(Some(&trace), 4, &instruction, 7, true, None)
            .expect_err("mismatched target must fail closed");

        assert_eq!(error.kind(), DiagnosticKind::TraceInput);
    }

    #[test]
    fn call_hash_classification_is_typed() {
        assert_eq!(
            classify_call_imm(ebpf::hash_symbol_name(b"sol_memset_")),
            CallImmClassification::ModeledSyscall(b"sol_memset_")
        );
        assert_eq!(
            classify_call_imm(ebpf::hash_symbol_name(b"sol_log_64_")),
            CallImmClassification::UnmodeledSyscall(b"sol_log_64_")
        );
        assert_eq!(
            classify_call_imm(0xfeed_beef),
            CallImmClassification::Unknown
        );
    }

    #[test]
    fn exit_disposition_distinguishes_top_level_and_nested_return() {
        let mut state = SymState::default();
        assert_eq!(exit_disposition(&state), ExitDisposition::TopLevel);

        state.push_call_frame(12, std::array::from_fn(|_| Expr::Const(0)));
        assert_eq!(exit_disposition(&state), ExitDisposition::NestedReturn);
    }

    #[test]
    fn retry_inputs_converge_into_plans() {
        let mut hot_regions = std::collections::BTreeMap::new();
        merge_hot_regions(
            &mut hot_regions,
            [("r1".to_string(), 0, 8), ("r1".to_string(), 8, 16)],
        );
        assert_eq!(hot_regions["r1"], vec![(0, 16)]);

        let mut blob_splits = std::collections::BTreeMap::new();
        merge_blob_splits(
            &mut blob_splits,
            [("r2".to_string(), 32, 8), ("r2".to_string(), 32, 16)],
        );
        assert_eq!(blob_splits[&("r2".to_string(), 32)], 16);
    }
}
