//! Shared program-analysis substrate for qedlift / qedrecover (issue #41).
//! Provides the canonical slot↔logical PC converter; previously duplicated in each tool,
//! causing the 2026-06-10 bug (slot 309 vs logical 304 for transfer's arm entry).
//! Trusted-input front-end (`docs/TCB.md` §5); wrong PC maps fail downstream `native_decide` pins.

use solana_sbpf::ebpf;

pub mod layout;
pub mod profile;
pub mod symbolicate;

/// Static-analysis `ContextObject`: the lifting tools load executables for analysis only and
/// never execute them, so metering is a no-op. Shared by qedlift and qedrecover.
pub struct NoopCtx;

impl solana_sbpf::vm::ContextObject for NoopCtx {
    fn consume(&mut self, _amount: u64) {}
    fn get_remaining(&self) -> u64 {
        0
    }
}

/// Converts between slot PC (raw 8-byte slot index; `lddw` = 2 slots; `cfg_nodes`/jump-`off` space)
/// and logical PC (decoded-array index; `lddw` = 1 element; Lean decode / qedlift / `.pcs` space).
/// The two agree until the first `lddw` and drift by 1 per `lddw` thereafter.
pub struct PcMap {
    /// `logical_to_slot[i]` = slot where logical instruction `i` begins.
    logical_to_slot: Vec<usize>,
    /// `slot_to_logical[s]` = logical index for slot `s` (both slots of an `lddw` resolve to it). `None` past the end.
    slot_to_logical: Vec<Option<usize>>,
}

impl PcMap {
    /// Build from the decoded (lddw-merged) instruction list. Each insn spans 2 slots for `lddw`, 1 otherwise,
    /// matching `Decode.decodeProgram` pass 1. One converter for both qedlift and qedrecover (issue #41).
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

    /// Logical index for `slot` (both slots of an `lddw` resolve to its logical index). `None` past the end.
    pub fn slot_to_logical(&self, slot: usize) -> Option<usize> {
        self.slot_to_logical.get(slot).copied().flatten()
    }

    /// Slot where logical instruction `logical` begins. `None` past the end.
    pub fn logical_to_slot(&self, logical: usize) -> Option<usize> {
        self.logical_to_slot.get(logical).copied()
    }

    /// Number of logical instructions.
    pub fn logical_len(&self) -> usize {
        self.logical_to_slot.len()
    }

    /// Resolve a slot-relative jump at `logical_pc` with raw `off` to the logical target PC,
    /// mirroring `Decode.decodeProgram`'s rewrite. Falls back to `logical_pc+1+off` for
    /// lddw-free fixtures and to the raw slot for malformed targets (fail loudly).
    pub fn resolve_jump_target(&self, logical_pc: usize, off: i64) -> i64 {
        match self.logical_to_slot.get(logical_pc) {
            Some(&slot) => {
                let target_slot = slot as i64 + 1 + off;
                if target_slot < 0 {
                    return target_slot; // out of range — render as-is
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

    // Only `.opc` matters to PcMap; other fields are zeroed.
    fn insn(opc: u8) -> ebpf::Insn {
        ebpf::Insn { ptr: 0, opc, dst: 0, src: 0, off: 0, imm: 0 }
    }

    #[test]
    fn lddw_free_is_identity() {
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
        // [mov, lddw, add, lddw, exit] → slots [0, 1+2, 3, 4+5, 6].
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
        // Both slots of each lddw must resolve to its logical index.
        assert_eq!(m.slot_to_logical(1), Some(1));
        assert_eq!(m.slot_to_logical(2), Some(1));
        assert_eq!(m.slot_to_logical(4), Some(3));
        assert_eq!(m.slot_to_logical(5), Some(3));
        assert_eq!(m.slot_to_logical(7), None);
    }
}
