use solana_sbpf::ebpf;

use crate::diagnostic::{DiagnosticKind, LiftError};

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
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_branch_taken(
    trace: Option<&[usize]>,
    ti: usize,
    pc_iter: usize,
    ins: &ebpf::Insn,
    jtgt: i64,
    is_cond_jump: bool,
    target_disc: Option<i64>,
) -> Result<Option<bool>, LiftError> {
    let branch_taken: Option<bool> = if let Some(t) = trace {
        if is_cond_jump {
            let next = t.get(ti + 1).copied();
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
            Some(taken)
        } else {
            None
        }
    } else {
        match (ins.opc, target_disc) {
            (ebpf::JEQ64_IMM, Some(td)) | (ebpf::JEQ32_IMM, Some(td)) => Some(ins.imm == td),
            (ebpf::JNE64_IMM, Some(td)) | (ebpf::JNE32_IMM, Some(td)) => Some(ins.imm != td),
            // JGT: take branch when td > imm (disc > N → upper_half pattern).
            (ebpf::JGT64_IMM, Some(td)) | (ebpf::JGT32_IMM, Some(td)) => Some(td > ins.imm),
            _ if is_cond_jump => Some(false), // default: not-taken
            _ => None,
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
    fn static_discriminator_decides_jeq_jne_and_jgt() {
        for (opc, imm, discriminator, expected) in [
            (ebpf::JEQ64_IMM, 7, 7, Some(true)),
            (ebpf::JEQ64_IMM, 7, 8, Some(false)),
            (ebpf::JNE64_IMM, 7, 8, Some(true)),
            (ebpf::JNE64_IMM, 7, 7, Some(false)),
            (ebpf::JGT64_IMM, 7, 8, Some(true)),
            (ebpf::JGT64_IMM, 7, 7, Some(false)),
        ] {
            let instruction = insn(opc, 2, imm);
            let decision =
                resolve_branch_taken(None, 0, 4, &instruction, 7, true, Some(discriminator))
                    .expect("static branch decision");
            assert_eq!(decision, expected);
        }
    }

    #[test]
    fn trace_decides_taken_and_fallthrough_branches() {
        let instruction = insn(ebpf::JEQ64_IMM, 2, 7);
        let fallthrough = resolve_branch_taken(Some(&[4, 5]), 0, 4, &instruction, 7, true, None)
            .expect("fall-through decision");
        let taken = resolve_branch_taken(Some(&[4, 7]), 0, 4, &instruction, 7, true, None)
            .expect("taken decision");

        assert_eq!(fallthrough, Some(false));
        assert_eq!(taken, Some(true));
    }

    #[test]
    fn trace_target_mismatch_is_a_typed_input_error() {
        let instruction = insn(ebpf::JEQ64_IMM, 2, 7);
        let error = resolve_branch_taken(Some(&[4, 9]), 0, 4, &instruction, 7, true, None)
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

        state
            .call_stack
            .push((12, std::array::from_fn(|_| Expr::Const(0))));
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
