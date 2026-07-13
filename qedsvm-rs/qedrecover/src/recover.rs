//! Overlay/IDL input types + dispatcher recognition, CFG slicing, and static arm
//! classification — everything between the parsed inputs and the emitters.

use std::collections::{BTreeSet, VecDeque};
use std::path::Path;

use solana_sbpf::{
    ebpf,
    static_analysis::{Analysis, CfgNode},
};

use qed_analysis::{
    layout::{codama_number_size, parse_account_layout, AccountLayout},
    PcMap,
};
pub(crate) use qed_artifacts::{
    CodamaIdl as Idl, IdlInstruction, Overlay, OverlayInstruction as OverlayIx,
};

use crate::idioms;

/// Classify a constant error-exit block. Three tail shapes: (1) `mov64/lddw r0, imm; exit`
/// in-block; (2) `mov64/lddw r0, imm; ja tgt` where tgt is a bare-exit block; (3) fall-through
/// into a bare-exit block. Returns `toU64 imm` (sign-extends, matching Lean). Each shape is
/// discharged by `errorExit{,_lddw}_spec` / `errorExitJa{,_lddw}_spec` (Terminating.lean).
pub(crate) fn error_exit_code(analysis: &Analysis, b: &CfgNode) -> Option<u64> {
    let r = &b.instructions;
    let dest_is_exit = || -> bool {
        if b.destinations.len() != 1 {
            return false;
        }
        analysis
            .cfg_nodes
            .get(&b.destinations[0])
            .map(|d| analysis.instructions[d.instructions.start].opc == ebpf::EXIT)
            .unwrap_or(false)
    };
    if r.end == r.start {
        return None;
    }
    let last = &analysis.instructions[r.end - 1];
    let scan_end = if last.opc == ebpf::EXIT || last.opc == ebpf::JA {
        if last.opc == ebpf::JA && !dest_is_exit() {
            return None;
        }
        r.end - 1
    } else {
        if !dest_is_exit() {
            return None;
        }
        r.end
    };
    // Scan backward for the last r0 write. Error landings can interleave spills between
    // the setter and terminator, so "insn right before jump" is too shallow. LD/LDX/ALU64/ALU32
    // write dst; a store's dst is the memory base (not written); call clobbers r0 non-constant.
    for idx in (r.start..scan_end).rev() {
        let insn = &analysis.instructions[idx];
        if insn.opc == ebpf::CALL_IMM || insn.opc == ebpf::CALL_REG {
            return None; // r0 is a call result, not a constant
        }
        let class = insn.opc & 0x07;
        let writes_reg = matches!(class, 0x00 | 0x01 | 0x04 | 0x07);
        if writes_reg && insn.dst == 0 {
            return match insn.opc {
                // `augment_lddw_unchecked` merges the high half, so `imm` is the full 64-bit value.
                ebpf::MOV64_IMM | ebpf::LD_DW_IMM => Some(insn.imm as u64),
                _ => None, // r0 written but not from a constant
            };
        }
    }
    None // r0 set by a predecessor
}

/// Parse a `.pcs` trace file (one decimal logical PC per line, `#` comments ignored).
pub(crate) fn load_trace(path: &Path) -> Result<BTreeSet<usize>, String> {
    let text =
        std::fs::read_to_string(path).map_err(|e| format!("--trace {}: {}", path.display(), e))?;
    let mut pcs = BTreeSet::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let pc: usize = line.parse().map_err(|_| {
            format!(
                "--trace {}: line {}: not a decimal PC ({:?})",
                path.display(),
                i + 1,
                line
            )
        })?;
        pcs.insert(pc);
    }
    if pcs.is_empty() {
        return Err(format!("--trace {}: no PCs found", path.display()));
    }
    Ok(pcs)
}

/// Map a Codama discriminator `format` to the sBPF load opcode (unsigned width only).
pub(crate) fn discriminator_load_opc(format: &str) -> Option<u8> {
    match format {
        "u8" => Some(ebpf::LD_B_REG),
        "u16" => Some(ebpf::LD_H_REG),
        "u32" => Some(ebpf::LD_W_REG),
        "u64" => Some(ebpf::LD_DW_REG),
        _ => None,
    }
}

/// Find the dispatcher arm for a discriminator value. Two shapes: `ldxX rD,[rS+0]; jeq rD,disc`
/// (taken branch = arm entry) and `jne rD,disc` (fall-through = arm entry). Load and jump may be
/// separated by other compares on the same register (subsequent arms in a cluster reuse the load).
///
/// Returns `(load_pc, jump_pc, arm_entry_pc)`. `load_pc`/`jump_pc` are logical (decoded-array
/// indices); `arm_entry_pc` is a raw slot PC (the space `cfg_nodes` keys use) — convert with
/// `slot_to_logical` before reporting or comparing with `.pcs` traces.
pub(crate) fn find_dispatch_arm(
    instructions: &[ebpf::Insn],
    start_pc: usize,
    load_opc: u8,
    disc_value: i64,
) -> Option<(usize, usize, usize)> {
    let n = instructions.len();
    // Solana ABI: program input is always r1. Restricting source to r1 avoids false matches
    // on account-parsing loads that also read offset 0 of other pointers.
    const INPUT_PTR_REG: u8 = 1;
    let mut pc = start_pc;
    while pc < n {
        let load = &instructions[pc];
        if load.opc != load_opc || load.off != 0 || load.src != INPUT_PTR_REG {
            pc += 1;
            continue;
        }
        let loaded_reg = load.dst;
        let window = 64.min(n - pc - 1);
        for k in 1..=window {
            let cur = &instructions[pc + k];
            if writes_dst(cur, loaded_reg) {
                break;
            } // cluster ended
            if cur.dst == loaded_reg && cur.imm == disc_value {
                let is_jeq = cur.opc == ebpf::JEQ32_IMM || cur.opc == ebpf::JEQ64_IMM;
                let is_jne = cur.opc == ebpf::JNE32_IMM || cur.opc == ebpf::JNE64_IMM;
                if is_jeq {
                    // Base must be `cur.ptr` (slot), NOT the vec index — mixing spaces
                    // was a real bug: p_token transfer returned 309 instead of slot 336.
                    let target = (cur.ptr as i64) + 1 + (cur.off as i64);
                    return Some((pc, pc + k, target as usize));
                }
                if is_jne {
                    return Some((pc, pc + k, cur.ptr + 1)); // not-taken = next slot
                }
            }
        }
        pc += 1;
    }
    None
}

/// True if `insn` writes `reg` (i.e. is not a compare-jump, which only reads dst).
fn writes_dst(insn: &ebpf::Insn, reg: u8) -> bool {
    if insn.dst != reg {
        return false;
    }
    let opc = insn.opc;
    let is_cmp_jump = matches!(
        opc,
        ebpf::JEQ32_IMM
            | ebpf::JEQ64_IMM
            | ebpf::JNE32_IMM
            | ebpf::JNE64_IMM
            | ebpf::JGT32_IMM
            | ebpf::JGT64_IMM
            | ebpf::JGE32_IMM
            | ebpf::JGE64_IMM
            | ebpf::JLT32_IMM
            | ebpf::JLT64_IMM
            | ebpf::JLE32_IMM
            | ebpf::JLE64_IMM
            | ebpf::JSGT32_IMM
            | ebpf::JSGT64_IMM
            | ebpf::JSGE32_IMM
            | ebpf::JSGE64_IMM
            | ebpf::JSLT32_IMM
            | ebpf::JSLT64_IMM
            | ebpf::JSLE32_IMM
            | ebpf::JSLE64_IMM
            | ebpf::JSET32_IMM
            | ebpf::JSET64_IMM
    );
    !is_cmp_jump
}

/// BFS over the CFG from `entry`. `bound` restricts the walk to a set of block-start PCs
/// (typically the enclosing function) so shared helpers don't leak into the arm slice.
pub(crate) fn slice_cfg<'a>(
    analysis: &'a Analysis<'a>,
    entry: usize,
    bound: Option<&BTreeSet<usize>>,
) -> Vec<&'a CfgNode> {
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    let mut blocks: Vec<&CfgNode> = Vec::new();
    queue.push_back(entry);
    while let Some(pc) = queue.pop_front() {
        if !visited.insert(pc) {
            continue;
        }
        if let Some(b) = bound {
            if !b.contains(&pc) {
                continue;
            }
        }
        if let Some(node) = analysis.cfg_nodes.get(&pc) {
            blocks.push(node);
            for &dest in &node.destinations {
                queue.push_back(dest);
            }
        }
    }
    blocks
}

pub(crate) struct Discriminator {
    pub(crate) value: i64,
    pub(crate) format: String,
    pub(crate) size: usize,
}

pub(crate) struct ConstExit {
    pub(crate) block_start: usize,
    pub(crate) exit_code: u64,
}

pub(crate) struct RecoveredArm<'a> {
    pub(crate) disc: Discriminator,
    pub(crate) load_pc: usize,
    pub(crate) jeq_pc: usize,
    pub(crate) arm_entry_slot: usize,
    pub(crate) arm_entry_logical: usize,
    pub(crate) enclosing_func_slot: usize,
    pub(crate) enclosing_func_logical: usize,
    pub(crate) func_block_count: usize,
    pub(crate) arm_blocks: Vec<&'a CfgNode>,
    pub(crate) arm_insns: usize,
    pub(crate) unconstrained_blocks: usize,
    pub(crate) exiting_block_count: usize,
    pub(crate) idiom_tags: Vec<idioms::Idiom>,
    pub(crate) const_exits: Vec<ConstExit>,
}

pub(crate) enum Recovery<'a> {
    Unsupported,
    DispatchMiss { disc: Discriminator },
    Arm(RecoveredArm<'a>),
}

pub(crate) fn collect_account_layouts(idl_value: &serde_json::Value) -> Vec<AccountLayout> {
    let Some(accounts) = idl_value
        .get("program")
        .unwrap_or(idl_value)
        .get("accounts")
        .and_then(|v| v.as_array())
    else {
        return Vec::new();
    };

    let mut layouts = Vec::new();
    for account in accounts {
        let Some(name) = account.get("name").and_then(|n| n.as_str()) else {
            continue;
        };
        if let Ok(layout) = parse_account_layout(idl_value, name) {
            layouts.push(layout);
        }
    }
    layouts.sort_by(|a, b| a.name.cmp(&b.name));
    layouts
}

pub(crate) fn validate_account_layout_bindings(
    overlay: &Overlay,
    idl: &Idl,
    layouts: &[AccountLayout],
) -> Result<(), String> {
    let layout_names: BTreeSet<&str> = layouts.iter().map(|l| l.name.as_str()).collect();
    for ovix in &overlay.instructions {
        let idl_ix = idl
            .program
            .instructions
            .iter()
            .find(|i| i.name == ovix.name)
            .ok_or_else(|| {
                format!(
                    "overlay names instruction `{}` but IDL has no such instruction",
                    ovix.name
                )
            })?;
        let role_names: BTreeSet<&str> = idl_ix.accounts.iter().map(|a| a.name.as_str()).collect();
        for (role, layout) in &ovix.account_layouts {
            if !role_names.contains(role.as_str()) {
                return Err(format!(
                    "overlay instruction `{}` binds unknown account role `{}`",
                    ovix.name, role
                ));
            }
            if !layout_names.contains(layout.as_str()) {
                return Err(format!(
                    "overlay instruction `{}` binds account role `{}` to unknown or unsupported account layout `{}`",
                    ovix.name, role, layout
                ));
            }
        }
    }
    Ok(())
}

/// Block-start PCs within the function enclosing `entry` (bounded by `analysis.functions`).
pub(crate) fn function_block_set(analysis: &Analysis, entry: usize) -> BTreeSet<usize> {
    let func_start = analysis
        .functions
        .range(..=entry)
        .next_back()
        .map(|(&k, _)| k)
        .unwrap_or(0);
    let func_end = analysis
        .functions
        .range((
            std::ops::Bound::Excluded(func_start),
            std::ops::Bound::Unbounded,
        ))
        .next()
        .map(|(&k, _)| k)
        .unwrap_or(analysis.instructions.len());
    analysis
        .cfg_nodes
        .range(func_start..func_end)
        .map(|(&k, _)| k)
        .collect()
}

pub(crate) fn discriminator_info(idl_ix: &IdlInstruction) -> Option<Discriminator> {
    let disc_arg = idl_ix
        .arguments
        .iter()
        .find(|a| a.name == "discriminator")?;
    let format = disc_arg.ty.get("format").and_then(|v| v.as_str())?;
    let value = disc_arg
        .default_value
        .as_ref()
        .and_then(|d| d.get("number"))
        .and_then(|n| n.as_i64())?;
    let size = codama_number_size(format)?;
    discriminator_load_opc(format)?;
    Some(Discriminator {
        value,
        format: format.to_string(),
        size,
    })
}

/// Dispatcher recognition, CFG slicing, and static arm classification for one IDL instruction.
pub(crate) fn recover_one<'a>(
    analysis: &'a Analysis<'a>,
    pc_map: &PcMap,
    idl_ix: &'a IdlInstruction,
) -> Result<Recovery<'a>, String> {
    let disc = match discriminator_info(idl_ix) {
        Some(d) => d,
        None => return Ok(Recovery::Unsupported),
    };
    let load_opc = discriminator_load_opc(&disc.format)
        .expect("discriminator_info filters unsupported discriminator formats");

    let (load_pc, jeq_pc, arm_entry) =
        match find_dispatch_arm(&analysis.instructions, 0, load_opc, disc.value) {
            Some(t) => t,
            None => return Ok(Recovery::DispatchMiss { disc }),
        };

    let func_set = function_block_set(analysis, arm_entry);
    let func_start = func_set.iter().next().copied().unwrap_or(arm_entry);
    let arm_blocks = slice_cfg(analysis, arm_entry, Some(&func_set));
    let arm_insns: usize = arm_blocks
        .iter()
        .map(|b| b.instructions.end - b.instructions.start)
        .sum();
    let unconstrained_blocks = slice_cfg(analysis, arm_entry, None).len();
    let exiting_block_count = arm_blocks
        .iter()
        .filter(|b| {
            b.destinations.is_empty() || b.destinations.iter().any(|d| !func_set.contains(d))
        })
        .count();
    let idiom_tags = idioms::scan_arm(analysis, &arm_blocks, Some((load_pc, disc.size)));
    let const_exits = arm_blocks
        .iter()
        .filter_map(|b| {
            error_exit_code(analysis, b).map(|exit_code| ConstExit {
                block_start: b.instructions.start,
                exit_code,
            })
        })
        .collect();
    let arm_entry_logical = pc_map.slot_to_logical(arm_entry).unwrap_or(arm_entry);
    let enclosing_func_logical = pc_map.slot_to_logical(func_start).unwrap_or(func_start);

    Ok(Recovery::Arm(RecoveredArm {
        disc,
        load_pc,
        jeq_pc,
        arm_entry_slot: arm_entry,
        arm_entry_logical,
        enclosing_func_slot: func_start,
        enclosing_func_logical,
        func_block_count: func_set.len(),
        arm_blocks,
        arm_insns,
        unconstrained_blocks,
        exiting_block_count,
        idiom_tags,
        const_exits,
    }))
}
