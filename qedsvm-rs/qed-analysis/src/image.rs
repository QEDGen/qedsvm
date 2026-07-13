//! Shared loading and decoded-instruction view of a compiled sBPF ELF.

use std::path::Path;
use std::sync::Arc;

use solana_sbpf::{ebpf, elf::Executable, program::BuiltinProgram};

use crate::{NoopCtx, PcMap};

/// One loaded program image reused across recovery, profiling, and lifting.
pub struct ProgramImage {
    pub elf_bytes: Vec<u8>,
    pub executable: Executable<NoopCtx>,
    pub text_offset: u64,
    pub text_bytes: Vec<u8>,
    pub insns: Vec<ebpf::Insn>,
    pub pc_map: PcMap,
}

impl ProgramImage {
    pub fn load(path: &Path) -> Result<Self, Box<dyn std::error::Error>> {
        let elf_bytes = std::fs::read(path)?;
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable = Executable::load(&elf_bytes, loader)?;
        let (text_offset, text) = executable.get_text_bytes();
        let text_bytes = text.to_vec();
        let mut insns = Vec::new();
        let mut slot = 0;
        while slot * ebpf::INSN_SIZE < text_bytes.len() {
            let mut insn = ebpf::get_insn(&text_bytes, slot);
            let opcode = insn.opc;
            if opcode == ebpf::LD_DW_IMM {
                ebpf::augment_lddw_unchecked(&text_bytes, &mut insn);
            }
            insns.push(insn);
            slot += if opcode == ebpf::LD_DW_IMM { 2 } else { 1 };
        }
        let pc_map = PcMap::from_insns(&insns);
        Ok(Self {
            elf_bytes,
            executable,
            text_offset,
            text_bytes,
            insns,
            pc_map,
        })
    }
}
