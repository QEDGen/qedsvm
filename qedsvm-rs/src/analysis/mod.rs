//! Shared program-analysis substrate for the qedlift / qedrecover pipeline.
//!
//! `docs/PIPELINE.md` frames qedrecover (STAGE 1, scope) and qedlift
//! (STAGE 3, prove) as two steps of one flow. Historically each tool
//! re-derived the base "analyse the asm" facts independently; issue #41
//! consolidates that substrate here so there is one source of truth.
//!
//! Phase 1 (this module): the slot<->logical PC converter, previously
//! duplicated as qedlift's `BinaryCtx` maps and qedrecover's
//! `slot_to_logical` binary-search over `analysis.instructions[].ptr`.
//! One converter retires the slot/logical confusion bug class (the
//! 2026-06-10 bug that rooted transfer's CFG slice at slot 309 instead
//! of logical 304; see qedrecover's `transfer_arm_entry_spaces` pin and
//! the equivalence pin `pc_map_matches_analysis_ptrs`).
//!
//! Soundness posture is unchanged: this is all trusted-input front-end
//! code (`docs/TCB.md` §5, audit H8). The kernel-checked per-PC decode
//! pins downstream make even a converter bug fail-closed (a wrong PC
//! map yields a failing `native_decide` pin, not an unsound proof).

use solana_sbpf::ebpf;

pub mod layout;

/// Converts between the two PC numberings the pipeline uses:
///
///   * **slot** PC: the raw 8-byte instruction-slot index. `lddw`
///     occupies two slots. This is the space jump `off` fields,
///     `cfg_nodes` keys, and `analysis.instructions[].ptr` live in.
///   * **logical** PC: the index into the decoded (lddw-merged)
///     instruction vector. This is the space the Lean decoder
///     (`Decode.decodeProgram`), qedlift's symbolic walker, and `.pcs`
///     execution traces live in.
///
/// The two agree up to the first `lddw` and drift by one slot per
/// `lddw` thereafter. Mirrors the slot map built by `Decode` pass 1.
pub struct PcMap {
    /// `logical_to_slot[i]` = the slot index where logical instruction
    /// `i` begins.
    logical_to_slot: Vec<usize>,
    /// `slot_to_logical[s]` = the logical index of the instruction
    /// occupying slot `s` (both slots of an `lddw` map to its logical
    /// index). `None` for slots past the end.
    slot_to_logical: Vec<Option<usize>>,
}

impl PcMap {
    /// Build from a decoded (lddw-merged) instruction list — the form
    /// both qedlift's walker (`BinaryCtx.insns`) and sbpf's
    /// `analysis.instructions` carry. Each instruction spans 2 slots for
    /// `lddw`, 1 otherwise, exactly as `Decode.decodeProgram` pass 1
    /// computes the Lean slot map. Building from the merged insns (not
    /// two independent decodes) is what makes this *one* converter for
    /// both consumers.
    pub fn from_insns(insns: &[ebpf::Insn]) -> PcMap {
        let mut logical_to_slot = Vec::with_capacity(insns.len());
        let mut slot_to_logical: Vec<Option<usize>> = Vec::new();
        let mut slot = 0usize;
        for (logical, insn) in insns.iter().enumerate() {
            logical_to_slot.push(slot);
            let span = if insn.opc == ebpf::LD_DW_IMM { 2 } else { 1 };
            for s in slot..slot + span {
                while slot_to_logical.len() <= s {
                    slot_to_logical.push(None);
                }
                slot_to_logical[s] = Some(logical);
            }
            slot += span;
        }
        PcMap { logical_to_slot, slot_to_logical }
    }

    /// The logical index occupying `slot` (both slots of an `lddw`
    /// resolve to the merged instruction's logical index). `None` past
    /// the end.
    pub fn slot_to_logical(&self, slot: usize) -> Option<usize> {
        self.slot_to_logical.get(slot).copied().flatten()
    }

    /// The slot where logical instruction `logical` begins. `None` past
    /// the end.
    pub fn logical_to_slot(&self, logical: usize) -> Option<usize> {
        self.logical_to_slot.get(logical).copied()
    }

    /// Number of logical instructions covered.
    pub fn logical_len(&self) -> usize {
        self.logical_to_slot.len()
    }

    /// Resolve a slot-relative jump from logical PC `logical_pc` with
    /// raw offset `off` to the *logical* target PC, mirroring how
    /// `Decode.decodeProgram` rewrites jump targets so the rendered
    /// `.jXX ... target` matches what `native_decide` proves. Falls back
    /// to `logical_pc + 1 + off` when the maps don't cover the PC (e.g. a
    /// synthetic fixture with no `lddw`, where slot == logical), and to
    /// the raw target slot when the target lands past the end or in the
    /// interior of an `lddw` (malformed) — rendered as-is to fail loudly.
    pub fn resolve_jump_target(&self, logical_pc: usize, off: i64) -> i64 {
        match self.logical_to_slot.get(logical_pc) {
            Some(&slot) => {
                let target_slot = slot as i64 + 1 + off;
                if target_slot < 0 {
                    return target_slot; // out of range; render as-is
                }
                match self.slot_to_logical(target_slot as usize) {
                    Some(logical) => logical as i64,
                    None => target_slot,
                }
            }
            None => logical_pc as i64 + 1 + off,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use solana_sbpf::ebpf;

    // A minimal insn with the given opcode (only `.opc` matters to PcMap).
    fn insn(opc: u8) -> ebpf::Insn {
        ebpf::Insn { ptr: 0, opc, dst: 0, src: 0, off: 0, imm: 0 }
    }

    #[test]
    fn lddw_free_is_identity() {
        // No lddw: slot == logical everywhere.
        let insns = vec![insn(ebpf::MOV64_IMM), insn(ebpf::ADD64_IMM), insn(ebpf::EXIT)];
        let m = PcMap::from_insns(&insns);
        for i in 0..insns.len() {
            assert_eq!(m.logical_to_slot(i), Some(i));
            assert_eq!(m.slot_to_logical(i), Some(i));
        }
        assert_eq!(m.logical_len(), 3);
        assert_eq!(m.slot_to_logical(3), None);
    }

    #[test]
    fn lddw_drifts_by_one_slot_each() {
        // [mov, lddw, add, lddw, exit] -> slots [0, 1(+2), 3, 4(+2), 6].
        let insns = vec![
            insn(ebpf::MOV64_IMM),  // logical 0 @ slot 0
            insn(ebpf::LD_DW_IMM),  // logical 1 @ slots 1,2
            insn(ebpf::ADD64_IMM),  // logical 2 @ slot 3
            insn(ebpf::LD_DW_IMM),  // logical 3 @ slots 4,5
            insn(ebpf::EXIT),       // logical 4 @ slot 6
        ];
        let m = PcMap::from_insns(&insns);
        assert_eq!(m.logical_to_slot(0), Some(0));
        assert_eq!(m.logical_to_slot(1), Some(1));
        assert_eq!(m.logical_to_slot(2), Some(3));
        assert_eq!(m.logical_to_slot(3), Some(4));
        assert_eq!(m.logical_to_slot(4), Some(6));
        // Both slots of each lddw resolve to its logical index.
        assert_eq!(m.slot_to_logical(1), Some(1));
        assert_eq!(m.slot_to_logical(2), Some(1));
        assert_eq!(m.slot_to_logical(4), Some(3));
        assert_eq!(m.slot_to_logical(5), Some(3));
        assert_eq!(m.slot_to_logical(7), None);
    }
}
