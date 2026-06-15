//! qedrecover — recover Lean metadata for a compiled Solana program from a `.so` + Codama IDL + qedsvm overlay.

mod idioms;

use std::collections::{BTreeSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use serde::Deserialize;
use solana_sbpf::{
    ebpf,
    elf::Executable,
    program::BuiltinProgram,
    static_analysis::{Analysis, CfgNode},
    vm::ContextObject,
};

use qed_analysis::{
    layout::{parse_account_layout, AccountLayout, FieldKind},
    PcMap,
};
use sha2::Digest;

#[derive(Debug, Deserialize)]
struct Overlay {
    idl: String,
    #[serde(rename = "instruction")]
    instructions: Vec<OverlayIx>,
}

#[derive(Debug, Deserialize)]
struct OverlayIx {
    name: String,
    // No claim fields are required; an unclaimed instruction is still recovered.
    refines: Option<String>,
    cu_budget: Option<u64>,
    /// Optional instruction-account role -> account-data layout binding.
    /// Example: `[instruction.account_layouts] source = "token"`.
    #[serde(default)]
    account_layouts: std::collections::BTreeMap<String, String>,
}

#[derive(Debug, Deserialize)]
struct Idl {
    program: IdlProgram,
}

#[derive(Debug, Deserialize)]
struct IdlProgram {
    name: String,
    #[serde(rename = "publicKey")]
    public_key: String,
    instructions: Vec<IdlInstruction>,
}

#[derive(Debug, Deserialize)]
struct IdlInstruction {
    name: String,
    accounts: Vec<IdlAccount>,
    arguments: Vec<IdlArgument>,
}

#[derive(Debug, Deserialize)]
struct IdlAccount {
    name: String,
    #[serde(rename = "isWritable", default)]
    is_writable: bool,
    #[serde(rename = "isSigner")]
    is_signer: serde_json::Value, // can be bool or "either"
}

#[derive(Debug, Deserialize)]
struct IdlArgument {
    name: String,
    // Opaque: many Codama type-node kinds; only `numberTypeNode` is special-cased at use time.
    #[serde(rename = "type")]
    ty: serde_json::Value,
    // Opaque: many Codama default-value node kinds; only `numberValueNode` is consumed.
    #[serde(rename = "defaultValue", default)]
    default_value: Option<serde_json::Value>,
}

// Static-analysis context — analysis doesn't execute.
struct NoopCtx;
impl ContextObject for NoopCtx {
    fn consume(&mut self, _amount: u64) {}
    fn get_remaining(&self) -> u64 {
        0
    }
}

struct Args {
    so: PathBuf,
    overlay: PathBuf,
    output: Option<PathBuf>,
    /// `.pcs` trace (one decimal logical PC per line, `#` comments ignored). Tags
    /// happy-path blocks in emitted metadata; rejected if overlay claims > 1 instruction.
    trace: Option<PathBuf>,
    /// Emit the qedmeta `.toml` sidecar (issue #37) consumed by qedlift. Independent of `--output`.
    qedmeta_out: Option<PathBuf>,
}

fn parse_args() -> Result<Args, String> {
    let mut so: Option<PathBuf> = None;
    let mut overlay: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut trace: Option<PathBuf> = None;
    let mut qedmeta_out: Option<PathBuf> = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--so" => so = Some(it.next().ok_or("--so needs a path")?.into()),
            "--overlay" => overlay = Some(it.next().ok_or("--overlay needs a path")?.into()),
            "--output" => output = Some(it.next().ok_or("--output needs a path")?.into()),
            "--trace" => trace = Some(it.next().ok_or("--trace needs a path")?.into()),
            "--qedmeta-out" => {
                qedmeta_out = Some(it.next().ok_or("--qedmeta-out needs a path")?.into())
            }
            other => return Err(format!("unknown arg: {}", other)),
        }
    }
    Ok(Args {
        so: so.ok_or("missing --so")?,
        overlay: overlay.ok_or("missing --overlay")?,
        output,
        trace,
        qedmeta_out,
    })
}

/// Classify a constant error-exit block. Three tail shapes: (1) `mov64/lddw r0, imm; exit`
/// in-block; (2) `mov64/lddw r0, imm; ja tgt` where tgt is a bare-exit block; (3) fall-through
/// into a bare-exit block. Returns `toU64 imm` (sign-extends, matching Lean). Each shape is
/// discharged by `errorExit{,_lddw}_spec` / `errorExitJa{,_lddw}_spec` (Terminating.lean).
fn error_exit_code(analysis: &Analysis, b: &CfgNode) -> Option<u64> {
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
fn load_trace(path: &Path) -> Result<BTreeSet<usize>, String> {
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

/// Size in bytes of a numeric type by Codama `format` string.
fn number_size(format: &str) -> Option<usize> {
    match format {
        "u8" | "i8" => Some(1),
        "u16" | "i16" => Some(2),
        "u32" | "i32" => Some(4),
        "u64" | "i64" => Some(8),
        _ => None,
    }
}

/// Map a Codama discriminator `format` to the sBPF load opcode (unsigned width only).
fn discriminator_load_opc(format: &str) -> Option<u8> {
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
fn find_dispatch_arm(
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
fn slice_cfg<'a>(
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

/// Cheap PascalCase conversion for Lean namespace names.
fn pascal(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut up = true;
    for c in s.chars() {
        if c == '_' || c == '-' {
            up = true;
            continue;
        }
        if up {
            out.extend(c.to_uppercase());
            up = false;
        } else {
            out.push(c);
        }
    }
    out
}

struct Discriminator {
    value: i64,
    format: String,
    size: usize,
}

struct ConstExit {
    block_start: usize,
    exit_code: u64,
}

struct RecoveredArm<'a> {
    disc: Discriminator,
    load_pc: usize,
    jeq_pc: usize,
    arm_entry_slot: usize,
    arm_entry_logical: usize,
    enclosing_func_slot: usize,
    enclosing_func_logical: usize,
    func_block_count: usize,
    arm_blocks: Vec<&'a CfgNode>,
    arm_insns: usize,
    unconstrained_blocks: usize,
    exiting_block_count: usize,
    idiom_tags: Vec<idioms::Idiom>,
    const_exits: Vec<ConstExit>,
}

enum Recovery<'a> {
    Unsupported,
    DispatchMiss { disc: Discriminator },
    Arm(RecoveredArm<'a>),
}

fn collect_account_layouts(idl_value: &serde_json::Value) -> Vec<AccountLayout> {
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

fn validate_account_layout_bindings(
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

fn field_kind_name(kind: &FieldKind) -> &'static str {
    match kind {
        FieldKind::Pubkey => "pubkey",
        FieldKind::U64 => "u64",
        FieldKind::Byte => "byte",
        FieldKind::Bytes(_) => "bytes",
    }
}

/// Emit the recovered arm metadata as a Lean module.
fn emit_lean<W: std::io::Write>(
    out: &mut W,
    args: &Args,
    overlay: &Overlay,
    ovix: &OverlayIx,
    idl_ix: &IdlInstruction,
    pc_map: &PcMap,
    recovered: &RecoveredArm<'_>,
    trace: Option<&BTreeSet<usize>>,
) -> std::io::Result<()> {
    let module = format!("QedRecover.{}", pascal(&ovix.name));
    let on_trace = |b: &CfgNode| -> bool {
        trace.is_some_and(|t| {
            t.range(b.instructions.start..b.instructions.end)
                .next()
                .is_some()
        })
    };

    writeln!(out, "/-")?;
    writeln!(
        out,
        "  Recovered metadata for the `{}` instruction in `{}`.",
        ovix.name,
        args.so
            .file_name()
            .map(|s| s.to_string_lossy())
            .unwrap_or_default()
    )?;
    writeln!(out, "  Generated by qedrecover — do not edit by hand.")?;
    writeln!(out)?;
    writeln!(out, "  Sources:")?;
    writeln!(out, "    .so:     {}", args.so.display())?;
    writeln!(out, "    overlay: {}", args.overlay.display())?;
    writeln!(out, "    idl:     {}", overlay.idl)?;
    writeln!(out)?;
    if trace.is_some() {
        writeln!(out, "  Happy-path tagging applied from an execution trace")?;
        writeln!(out, "  (`--trace`, captured via scripts/capture_trace.sh).")?;
        writeln!(
            out,
            "  `happyPathBlocks` lists the block-start PCs the trace"
        )?;
        writeln!(
            out,
            "  executed; the remaining `reachableBlocks` entries were not"
        )?;
        writeln!(
            out,
            "  on the traced path (error handlers and untaken branches)."
        )?;
    } else {
        writeln!(
            out,
            "  Happy/sad-path tagging NOT applied (no `--trace` given)."
        )?;
        writeln!(
            out,
            "  `reachableBlocks` lists every block reachable from the arm"
        )?;
        writeln!(
            out,
            "  entry within its enclosing function — both happy and sad."
        )?;
    }
    writeln!(out, "-/")?;
    writeln!(out)?;
    // Long literal lists (a correctly-rooted slice can be thousands of
    // blocks) blow Lean's default elaborator recursion depth.
    writeln!(out, "set_option maxRecDepth 65536")?;
    writeln!(out)?;
    writeln!(out, "namespace {}", module)?;
    writeln!(out)?;

    // `refines`/`cu_budget` are optional; emit empty/0 sentinels so the generated Lean is well-formed.
    writeln!(
        out,
        "/-- The MIR intrinsic this instruction claims to refine. -/"
    )?;
    writeln!(
        out,
        "def refinesIntrinsic : String := \"{}\"",
        ovix.refines.as_deref().unwrap_or("")
    )?;
    writeln!(out)?;
    writeln!(out, "/-- CU budget claimed by the overlay. -/")?;
    writeln!(out, "def cuBudget : Nat := {}", ovix.cu_budget.unwrap_or(0))?;
    writeln!(out)?;

    writeln!(
        out,
        "/-- Account roles, in instruction-account order (from IDL). -/"
    )?;
    writeln!(out, "def accountRoles : List String :=")?;
    writeln!(out, "  [")?;
    for (i, acc) in idl_ix.accounts.iter().enumerate() {
        let sep = if i + 1 < idl_ix.accounts.len() {
            ","
        } else {
            ""
        };
        writeln!(out, "    \"{}\"{}", acc.name, sep)?;
    }
    writeln!(out, "  ]")?;
    writeln!(out)?;

    writeln!(
        out,
        "/-- Discriminator value selecting this instruction. -/"
    )?;
    writeln!(
        out,
        "def discriminatorValue : Nat := {}",
        recovered.disc.value
    )?;
    writeln!(
        out,
        "/-- Discriminator width in bytes (from IDL number type). -/"
    )?;
    writeln!(
        out,
        "def discriminatorWidth : Nat := {}",
        recovered.disc.size
    )?;
    writeln!(out)?;

    writeln!(
        out,
        "/-- Recovered dispatcher site, in logical PC space (decoded-array"
    )?;
    writeln!(
        out,
        "    index, `lddw` = one element — matches Lean decode, qedlift,"
    )?;
    writeln!(out, "    and `.pcs` trace numbering). -/")?;
    writeln!(out, "def dispatchLoadPc : Nat := {}", recovered.load_pc)?;
    writeln!(out, "def dispatchJeqPc  : Nat := {}", recovered.jeq_pc)?;
    writeln!(
        out,
        "def armEntryPc     : Nat := {}",
        recovered.arm_entry_logical
    )?;
    writeln!(out)?;

    // Destinations are slot-space cfg keys; convert to logical. Unresolvable keys emitted as-is.
    writeln!(
        out,
        "/-- Reachable basic blocks from the arm entry, bounded to the"
    )?;
    writeln!(
        out,
        "    enclosing function. Entries are `(startPc, endPc, destinations)`"
    )?;
    writeln!(
        out,
        "    where `endPc` is exclusive and destinations are block-start PCs."
    )?;
    writeln!(
        out,
        "    All PCs logical (same space as the other defs here). -/"
    )?;
    writeln!(out, "def reachableBlocks : List (Nat × Nat × List Nat) :=")?;
    writeln!(out, "  [")?;
    for (i, b) in recovered.arm_blocks.iter().enumerate() {
        let dests = b
            .destinations
            .iter()
            .map(|&d| pc_map.slot_to_logical(d).unwrap_or(d).to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let sep = if i + 1 < recovered.arm_blocks.len() {
            ","
        } else {
            ""
        };
        writeln!(
            out,
            "    ({}, {}, [{}]){}",
            b.instructions.start, b.instructions.end, dests, sep
        )?;
    }
    writeln!(out, "  ]")?;
    writeln!(out)?;

    writeln!(
        out,
        "/-- Blocks that exit with a CONSTANT r0 (directly, or via a jump /"
    )?;
    writeln!(out, "    fall-through to a shared bare-`exit` block), as")?;
    writeln!(
        out,
        "    `(blockStartPc, exitCode)`. Code 0 entries are the success"
    )?;
    writeln!(
        out,
        "    funnels; nonzero entries are constant error landings. Each is"
    )?;
    writeln!(
        out,
        "    discharged in one `apply` of `errorExit{{,Ja}}{{,_lddw}}_spec`"
    )?;
    writeln!(out, "    (InstructionSpecs/Terminating.lean). -/")?;
    writeln!(out, "def constExitBlocks : List (Nat × Nat) :=")?;
    writeln!(
        out,
        "  [{}]",
        recovered
            .const_exits
            .iter()
            .map(|exit| format!("({}, {})", exit.block_start, exit.exit_code))
            .collect::<Vec<_>>()
            .join(", ")
    )?;
    writeln!(out)?;

    writeln!(
        out,
        "/-- Recognised instruction idioms, as `(pc, tag)` — the asm-side"
    )?;
    writeln!(
        out,
        "    domain vocabulary. `u64_field_{{increment,decrement}}` is the"
    )?;
    writeln!(
        out,
        "    balance-mutation triple; `error_propagation_check` marks a"
    )?;
    writeln!(
        out,
        "    call whose r0 result is branch-tested (the compiled `Err(e)`"
    )?;
    writeln!(
        out,
        "    propagation seam); `read_discriminator` is the dispatch load. -/"
    )?;
    writeln!(out, "def idioms : List (Nat × String) :=")?;
    writeln!(out, "  [")?;
    for (i, idm) in recovered.idiom_tags.iter().enumerate() {
        let sep = if i + 1 < recovered.idiom_tags.len() {
            ","
        } else {
            ""
        };
        writeln!(
            out,
            "    ({}, \"{} {}\"){}",
            idm.pc, idm.name, idm.detail, sep
        )?;
    }
    writeln!(out, "  ]")?;
    writeln!(out)?;

    if let Some(t) = trace {
        let happy: Vec<usize> = recovered
            .arm_blocks
            .iter()
            .filter(|b| on_trace(b))
            .map(|b| b.instructions.start)
            .collect();
        writeln!(
            out,
            "/-- Block-start PCs the execution trace passed through — the"
        )?;
        writeln!(
            out,
            "    happy path of this instruction, in block order. Blocks in"
        )?;
        writeln!(
            out,
            "    `reachableBlocks` but not here were never executed by the"
        )?;
        writeln!(out, "    trace (error handlers / untaken branches). -/")?;
        writeln!(out, "def happyPathBlocks : List Nat :=")?;
        writeln!(
            out,
            "  [{}]",
            happy
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        writeln!(out)?;
        writeln!(out, "/-- Number of PCs in the source trace. -/")?;
        writeln!(out, "def tracePcCount : Nat := {}", t.len())?;
        writeln!(out)?;
    }

    writeln!(out, "/-- Sanity-check totals. -/")?;
    writeln!(
        out,
        "def blockCount        : Nat := {}",
        recovered.arm_blocks.len()
    )?;
    writeln!(
        out,
        "def totalInstructions : Nat := {}",
        recovered.arm_insns
    )?;
    writeln!(out)?;

    writeln!(out, "end {}", module)?;

    Ok(())
}

/// Emit the qedmeta `.toml` sidecar (issue #37/#41 producer half). Schema v2: populates
/// `[instruction.recovered]`, `[[instruction.idiom]]`, `[[instruction.const_exit]]`, and
/// `[[instruction.tag]]`. Does NOT emit `[instruction.proofs]` — that links a Lean theorem
/// that only the human/qedgen author can assert. All PCs are logical (decoded-array indices).
fn emit_qedmeta<W: std::io::Write>(
    out: &mut W,
    overlay: &Overlay,
    ovix: &OverlayIx,
    idl: &Idl,
    idl_ix: &IdlInstruction,
    account_layouts: &[AccountLayout],
    so_sha256: &str,
    idl_sha256: &str,
    recovered: &RecoveredArm<'_>,
    trace: Option<&BTreeSet<usize>>,
) -> std::io::Result<()> {
    writeln!(
        out,
        "# qedmeta sidecar — emitted by qedrecover (do not edit by hand)."
    )?;
    writeln!(out, "# Schema: see qedsvm-rs/spec/qedmeta.md.")?;
    writeln!(out)?;
    writeln!(out, "schema_version = 2")?;
    writeln!(out, "spec_version   = \"qedmeta/0.2\"")?;
    writeln!(out)?;

    writeln!(out, "[target]")?;
    writeln!(out, "sha256       = \"{}\"", so_sha256)?;
    writeln!(out, "program_name = \"{}\"", idl.program.name)?;
    writeln!(out, "program_id   = \"{}\"", idl.program.public_key)?;
    writeln!(out)?;

    writeln!(out, "[idl]")?;
    writeln!(out, "format = \"codama\"")?;
    writeln!(out, "inline = false")?;
    writeln!(out, "ref    = \"{}\"", overlay.idl)?;
    writeln!(out, "sha256 = \"{}\"", idl_sha256)?;
    writeln!(out)?;

    for layout in account_layouts {
        writeln!(out, "[[account_layout]]")?;
        writeln!(out, "name   = \"{}\"", layout.name)?;
        writeln!(out, "source = \"codama\"")?;
        writeln!(out, "size   = {}", layout.size)?;
        writeln!(out)?;
        for field in &layout.fields {
            writeln!(out, "[[account_layout.field]]")?;
            writeln!(out, "name        = \"{}\"", field.name)?;
            writeln!(out, "offset      = {}", field.offset)?;
            writeln!(out, "kind        = \"{}\"", field_kind_name(&field.kind))?;
            if let FieldKind::Bytes(n) = &field.kind {
                writeln!(out, "width_bytes = {}", n)?;
            }
        }
        writeln!(out)?;
    }

    writeln!(out, "[[instruction]]")?;
    writeln!(out, "name      = \"{}\"", idl_ix.name)?;
    if let Some(r) = ovix.refines.as_ref() {
        writeln!(out, "refines   = \"{}\"", r)?;
    }
    if let Some(cu) = ovix.cu_budget {
        writeln!(out, "cu_budget = {}", cu)?;
    }
    writeln!(out)?;

    writeln!(out, "[instruction.discriminator]")?;
    writeln!(out, "value       = {}", recovered.disc.value)?;
    writeln!(out, "width_bytes = {}", recovered.disc.size)?;
    writeln!(out, "format      = \"{}\"", recovered.disc.format)?;
    writeln!(out)?;

    for acc in &idl_ix.accounts {
        writeln!(out, "[[instruction.account]]")?;
        writeln!(out, "name     = \"{}\"", acc.name)?;
        writeln!(out, "writable = {}", acc.is_writable)?;
        match &acc.is_signer {
            serde_json::Value::Bool(b) => writeln!(out, "signer   = {}", b)?,
            serde_json::Value::String(s) => writeln!(out, "signer   = \"{}\"", s)?,
            _ => writeln!(out, "signer   = false")?,
        }
        if let Some(layout) = ovix.account_layouts.get(&acc.name) {
            writeln!(out, "layout   = \"{}\"", layout)?;
        }
    }
    writeln!(out)?;

    // recovered facts — the section qedlift consumes
    writeln!(out, "[instruction.recovered]")?;
    writeln!(out, "dispatch_load_pc   = {}", recovered.load_pc)?;
    writeln!(out, "dispatch_jeq_pc    = {}", recovered.jeq_pc)?;
    writeln!(out, "arm_entry_pc       = {}", recovered.arm_entry_logical)?;
    writeln!(
        out,
        "enclosing_func_pc  = {}",
        recovered.enclosing_func_logical
    )?;
    writeln!(out, "block_count        = {}", recovered.arm_blocks.len())?;
    writeln!(out, "total_instructions = {}", recovered.arm_insns)?;
    // Full slice elided (1940 rows on p_token); qedlift consumes `arm_entry_pc` not the slice.
    // The `.recovered.lean` (--output) carries `reachableBlocks` for inspection.
    writeln!(out, "blocks = []")?;
    writeln!(out)?;

    for idm in &recovered.idiom_tags {
        writeln!(out, "[[instruction.idiom]]")?;
        writeln!(out, "pc      = {}", idm.pc)?;
        writeln!(out, "pattern = \"{}\"", idm.name)?;
        writeln!(out, "detail  = \"{}\"", idm.detail)?;
    }
    if !recovered.idiom_tags.is_empty() {
        writeln!(out)?;
    }

    for exit in &recovered.const_exits {
        writeln!(out, "[[instruction.const_exit]]")?;
        writeln!(out, "block_start = {}", exit.block_start)?;
        writeln!(out, "exit_code   = {}", exit.exit_code)?;
        writeln!(
            out,
            "role        = \"{}\"",
            if exit.exit_code == 0 {
                "success"
            } else {
                "error"
            }
        )?;
    }

    if let Some(t) = trace {
        for b in &recovered.arm_blocks {
            if t.range(b.instructions.start..b.instructions.end)
                .next()
                .is_some()
            {
                writeln!(out, "[[instruction.tag]]")?;
                writeln!(out, "block_start = {}", b.instructions.start)?;
                writeln!(out, "role        = \"happy\"")?;
            }
        }
    }

    Ok(())
}

/// Block-start PCs within the function enclosing `entry` (bounded by `analysis.functions`).
fn function_block_set(analysis: &Analysis, entry: usize) -> BTreeSet<usize> {
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

fn discriminator_info(idl_ix: &IdlInstruction) -> Option<Discriminator> {
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
    let size = number_size(format)?;
    discriminator_load_opc(format)?;
    Some(Discriminator {
        value,
        format: format.to_string(),
        size,
    })
}

/// Dispatcher recognition, CFG slicing, and static arm classification for one IDL instruction.
fn recover_one<'a>(
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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = parse_args().map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

    let overlay_text = std::fs::read_to_string(&args.overlay)?;
    let overlay: Overlay = toml::from_str(&overlay_text)?;
    let overlay_by_name: std::collections::BTreeMap<&str, &OverlayIx> = overlay
        .instructions
        .iter()
        .map(|ix| (ix.name.as_str(), ix))
        .collect();

    // IDL path is relative to the overlay file.
    let overlay_dir: &Path = args.overlay.parent().unwrap_or(Path::new("."));
    let idl_path = overlay_dir.join(&overlay.idl);
    let idl_text = std::fs::read_to_string(&idl_path)?;
    let idl: Idl = serde_json::from_str(&idl_text)?;
    let idl_value: serde_json::Value = serde_json::from_str(&idl_text)?;
    let account_layouts = collect_account_layouts(&idl_value);
    validate_account_layout_bindings(&overlay, &idl, &account_layouts)
        .map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

    let bytes = std::fs::read(&args.so)?;
    let loader = Arc::new(BuiltinProgram::new_mock());
    let executable: Executable<NoopCtx> = Executable::load(&bytes, loader)?;
    let analysis = Analysis::from_executable(&executable)?;
    // Shared with qedlift; pinned to agree with `analysis.instructions[].ptr` by issue #41 test.
    let pc_map = PcMap::from_insns(&analysis.instructions);

    println!("=== inputs ===");
    println!("  .so:     {}", args.so.display());
    println!("  overlay: {}", args.overlay.display());
    println!(
        "  idl:     {} (program {} @ {})",
        idl_path.display(),
        idl.program.name,
        idl.program.public_key
    );
    println!();

    println!("=== ELF analysis ===");
    println!("  entrypoint:   pc 0x{:x}", analysis.entrypoint);
    println!("  instructions: {}", analysis.instructions.len());
    println!("  basic blocks: {}", analysis.cfg_nodes.len());
    println!("  functions:    {}", analysis.functions.len());
    println!("  account layouts: {}", account_layouts.len());
    println!();

    // Overlay claims decorate the summary line but their absence does NOT skip recovery.
    println!("=== whole-program recovery ===");
    println!(
        "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
        "instruction", "disc", "dispatch (pc)", "armPc", "blks", "insns", "claim"
    );
    println!("  {}", "-".repeat(96));

    let mut total = 0usize;
    let mut recovered_ok = 0usize;
    let mut dispatch_miss = 0usize;
    let mut idl_unsupp = 0usize;

    for idl_ix in &idl.program.instructions {
        total += 1;
        let ov = overlay_by_name.get(idl_ix.name.as_str()).copied();
        let claim = match ov {
            Some(o) => {
                let refines = o.refines.as_deref().unwrap_or("?");
                let cu = o.cu_budget.map(|c| format!("CU={}", c)).unwrap_or_default();
                format!("{} {}", refines, cu).trim().to_string()
            }
            None => String::new(),
        };

        match recover_one(&analysis, &pc_map, idl_ix)? {
            Recovery::Unsupported => {
                idl_unsupp += 1;
                println!(
                    "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                    idl_ix.name, "—", "skip (idl)", "—", "—", "—", claim
                );
            }
            Recovery::DispatchMiss { disc } => {
                dispatch_miss += 1;
                println!(
                    "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                    idl_ix.name, disc.value, "not found", "—", "—", "—", claim
                );
            }
            Recovery::Arm(r) => {
                recovered_ok += 1;
                let dpc = format!("{}/{}", r.load_pc, r.jeq_pc);
                println!(
                    "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                    idl_ix.name,
                    r.disc.value,
                    dpc,
                    r.arm_entry_logical,
                    r.arm_blocks.len(),
                    r.arm_insns,
                    claim
                );
            }
        }
    }

    println!("  {}", "-".repeat(96));
    println!(
        "  recovered: {}/{}   dispatch-miss: {}   idl-skipped: {}",
        recovered_ok, total, dispatch_miss, idl_unsupp
    );
    if recovered_ok < total {
        println!();
        println!("  legend:");
        println!(
            "    skip (idl)    — IDL shape qedrecover can't analyse yet (non-number arg, etc.)"
        );
        println!(
            "    not found     — IDL shape OK but no `ldx + jeq imm=<disc>` pair in the binary"
        );
    }
    println!();

    // Detailed pass for overlay-claimed instructions. Multi-instruction --output (directory) not yet implemented.
    let claimed: Vec<&OverlayIx> = overlay
        .instructions
        .iter()
        .filter(|o| o.refines.is_some())
        .collect();
    let trace_pcs = match args.trace.as_ref() {
        Some(p) => {
            if claimed.len() != 1 {
                return Err(format!(
                    "--trace is per-instruction but the overlay claims {} \
                     instructions; narrow the overlay to one",
                    claimed.len()
                )
                .into());
            }
            // Trace PCs are logical indices matching `CfgNode.instructions` ranges; no slot conversion.
            Some(load_trace(p)?)
        }
        None => None,
    };
    if !claimed.is_empty() {
        println!("=== detailed view (overlay-claimed) ===");
    }
    for ovix in claimed {
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

        println!("  instruction: {}", ovix.name);
        println!("    refines:    {}", ovix.refines.as_deref().unwrap_or("—"));
        println!(
            "    cu_budget:  {}",
            ovix.cu_budget
                .map(|c| c.to_string())
                .unwrap_or_else(|| "—".to_string())
        );

        // Only numberTypeNode args have a fixed byte size; others abort (unsupported).
        let mut off: usize = 0;
        let mut disc_value: Option<i64> = None;
        println!("    ix_data:");
        for arg in &idl_ix.arguments {
            let kind = arg.ty.get("kind").and_then(|v| v.as_str()).unwrap_or("?");
            let format = arg
                .ty
                .get("format")
                .and_then(|v| v.as_str())
                .ok_or_else(|| {
                    format!(
                        "arg `{}` has non-number type ({}), unsupported in spike",
                        arg.name, kind
                    )
                })?;
            let sz = number_size(format)
                .ok_or_else(|| format!("unsupported number format: {}", format))?;
            // `numberValueNode` carries the literal under "number"; other kinds are skipped.
            let default = arg
                .default_value
                .as_ref()
                .and_then(|d| d.get("number"))
                .and_then(|n| n.as_i64());
            if arg.name == "discriminator" {
                disc_value = default;
            }
            let default_str = default.map(|n| format!(" = {}", n)).unwrap_or_default();
            println!(
                "      [{:#x}..{:#x}] {} : {}{}",
                off,
                off + sz,
                arg.name,
                format,
                default_str
            );
            off += sz;
        }

        if let Some(v) = disc_value {
            println!(
                "    discriminator: u8 = {} (looks for `ldxb`/`ldxw` + `jeq imm = {}`)",
                v, v
            );
        }

        println!("    accounts:");
        for (i, acc) in idl_ix.accounts.iter().enumerate() {
            let signer = match &acc.is_signer {
                serde_json::Value::Bool(b) => {
                    if *b {
                        "signer"
                    } else {
                        "—"
                    }
                }
                serde_json::Value::String(s) if s == "either" => "signer?",
                _ => "—",
            };
            let writ = if acc.is_writable { "writable" } else { "ro" };
            let layout = ovix
                .account_layouts
                .get(&acc.name)
                .map(|l| format!(" layout={}", l))
                .unwrap_or_default();
            println!(
                "      [{}] {:14} {} {}{}",
                i, acc.name, writ, signer, layout
            );
        }

        match recover_one(&analysis, &pc_map, idl_ix)? {
            Recovery::Unsupported => {
                if disc_value.is_some() {
                    println!("    [skip recognition: unsupported discriminator shape]");
                } else {
                    println!("    [skip recognition: no numeric discriminator value]");
                }
            }
            Recovery::DispatchMiss { disc } => {
                println!(
                    "    dispatch:    NOT FOUND \
                          (no `{}` + `jeq imm={}` pair from entry)",
                    disc.format, disc.value
                );
            }
            Recovery::Arm(recovered) => {
                println!("    dispatch:");
                println!("      discriminator load:  pc {}", recovered.load_pc);
                println!(
                    "      jeq imm={}:           pc {}",
                    recovered.disc.value, recovered.jeq_pc
                );
                println!(
                    "      → arm entry:         pc {} (slot {})",
                    recovered.arm_entry_logical, recovered.arm_entry_slot
                );

                println!(
                    "      enclosing function: pc {} ({} blocks)",
                    recovered.enclosing_func_slot, recovered.func_block_count
                );

                println!("    arm slice (function-bounded):");
                println!(
                    "      basic blocks: {} (unconstrained: {})",
                    recovered.arm_blocks.len(),
                    recovered.unconstrained_blocks
                );
                println!("      instructions: {}", recovered.arm_insns);
                println!(
                    "      blocks with exits outside the function: {}",
                    recovered.exiting_block_count
                );

                {
                    let mut counts: std::collections::BTreeMap<&str, usize> =
                        std::collections::BTreeMap::new();
                    for idm in &recovered.idiom_tags {
                        *counts.entry(idm.name).or_default() += 1;
                    }
                    let rendered = counts
                        .iter()
                        .map(|(n, c)| format!("{} x{}", n, c))
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!(
                        "      idioms: {}",
                        if rendered.is_empty() {
                            "none".to_string()
                        } else {
                            rendered
                        }
                    );
                }

                let (n_zero, n_nonzero) =
                    recovered
                        .const_exits
                        .iter()
                        .fold((0usize, 0usize), |(z, nz), code| {
                            if code.exit_code == 0 {
                                (z + 1, nz)
                            } else {
                                (z, nz + 1)
                            }
                        });
                println!(
                    "      constant-exit blocks: {} success (code 0), {} error",
                    n_zero, n_nonzero
                );

                if let Some(t) = trace_pcs.as_ref() {
                    let happy = recovered
                        .arm_blocks
                        .iter()
                        .filter(|b| {
                            t.range(b.instructions.start..b.instructions.end)
                                .next()
                                .is_some()
                        })
                        .count();
                    println!(
                        "      happy-path blocks (on trace): {}/{} ({} traced PCs)",
                        happy,
                        recovered.arm_blocks.len(),
                        t.len()
                    );
                }

                if let Some(path) = &args.output {
                    let mut f = std::fs::File::create(path)?;
                    emit_lean(
                        &mut f,
                        &args,
                        &overlay,
                        ovix,
                        idl_ix,
                        &pc_map,
                        &recovered,
                        trace_pcs.as_ref(),
                    )?;
                    println!();
                    println!("=== emitted Lean metadata ===");
                    println!("  output: {}", path.display());
                } else {
                    println!();
                    println!("=== Lean metadata (stdout) ===");
                    let stdout = std::io::stdout();
                    let mut lock = stdout.lock();
                    emit_lean(
                        &mut lock,
                        &args,
                        &overlay,
                        ovix,
                        idl_ix,
                        &pc_map,
                        &recovered,
                        trace_pcs.as_ref(),
                    )?;
                }

                if let Some(meta_path) = &args.qedmeta_out {
                    let hex = |d: &[u8]| d.iter().map(|b| format!("{:02x}", b)).collect::<String>();
                    let so_sha256 = hex(&sha2::Sha256::digest(&bytes));
                    let idl_sha256 = hex(&sha2::Sha256::digest(idl_text.as_bytes()));
                    let mut f = std::fs::File::create(meta_path)?;
                    emit_qedmeta(
                        &mut f,
                        &overlay,
                        ovix,
                        &idl,
                        idl_ix,
                        &account_layouts,
                        &so_sha256,
                        &idl_sha256,
                        &recovered,
                        trace_pcs.as_ref(),
                    )?;
                    println!();
                    println!("=== emitted qedmeta sidecar ===");
                    println!("  output: {}", meta_path.display());
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pins slot-vs-logical space correctness on p_token. Computing the jump target from the
    /// vec index (not `insn.ptr`) was a real bug: transfer's arm returned as 309 instead of
    /// slot 336 / logical 304. Ground truth: `p_token_transfer.pcs` trace jumps 199 -> 304.
    #[test]
    fn transfer_arm_entry_spaces() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let (load_pc, jeq_pc, arm_entry_slot) =
            find_dispatch_arm(&analysis.instructions, 0, ebpf::LD_B_REG, 3)
                .expect("find transfer dispatch arm");

        assert_eq!((load_pc, jeq_pc), (198, 199), "dispatcher site moved");
        assert_eq!(arm_entry_slot, 336, "arm entry must be a slot PC");
        let pc_map = PcMap::from_insns(&analysis.instructions);
        assert_eq!(
            pc_map.slot_to_logical(arm_entry_slot),
            Some(304),
            "slot 336 must resolve to logical 304 (the PC the trace jumps to)"
        );

        let func_set = function_block_set(&analysis, arm_entry_slot);
        let arm_blocks = slice_cfg(&analysis, arm_entry_slot, Some(&func_set));
        let trace = load_trace(Path::new("../tests/fixtures/p_token_transfer.pcs"))
            .expect("load transfer trace");
        let happy = arm_blocks
            .iter()
            .filter(|b| {
                trace
                    .range(b.instructions.start..b.instructions.end)
                    .next()
                    .is_some()
            })
            .count();
        assert_eq!(
            happy, 27,
            "happy-path tagging drifted: expected 27 on-trace blocks, got {}",
            happy
        );

        // p_token transfer errors return computed r0 through calls; only the nine r0=0 success
        // funnels are constant exits. A nonzero hit = detector tagging computed codes (bug).
        let codes: Vec<u64> = arm_blocks
            .iter()
            .filter_map(|b| error_exit_code(&analysis, b))
            .collect();
        assert_eq!(codes.len(), 9, "constant-exit block count drifted");
        assert!(
            codes.iter().all(|&c| c == 0),
            "transfer arm has no constant nonzero exits; got {:?}",
            codes
        );
    }

    /// Issue #41: `PcMap` must agree with `analysis.instructions[].ptr` so qedrecover can use
    /// the shared converter instead of its former `binary_search`-over-`.ptr`. Full round-trip.
    #[test]
    fn pc_map_matches_analysis_ptrs() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let pc_map = PcMap::from_insns(&analysis.instructions);
        assert_eq!(
            pc_map.logical_len(),
            analysis.instructions.len(),
            "shared PcMap covers a different instruction count than analysis"
        );
        for (logical, insn) in analysis.instructions.iter().enumerate() {
            assert_eq!(
                pc_map.logical_to_slot(logical),
                Some(insn.ptr),
                "logical {} maps to a different slot than analysis .ptr",
                logical
            );
            assert_eq!(
                pc_map.slot_to_logical(insn.ptr),
                Some(logical),
                "slot {} (logical {}) failed to round-trip",
                insn.ptr,
                logical
            );
        }
    }

    /// Pins `error_exit_code` against two real p_token shapes: shape 1 `lddw r0,19<<32; exit`
    /// (dispatch-mismatch at logical 196) and shape 2 `lddw r0,10<<32; ja <bare exit>` (logical 124).
    #[test]
    fn entrypoint_error_landings_classify() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let block_containing = |logical: usize| -> &CfgNode {
            analysis
                .cfg_nodes
                .values()
                .find(|b| b.instructions.start <= logical && logical < b.instructions.end)
                .expect("block containing pc")
        };
        assert_eq!(
            error_exit_code(&analysis, block_containing(196)),
            Some(19u64 << 32),
            "dispatch-mismatch landing misclassified"
        );
        assert_eq!(
            error_exit_code(&analysis, block_containing(124)),
            Some(10u64 << 32),
            "prelude ja-landing misclassified"
        );
    }

    /// Idiom recogniser: pins debit/credit pair, dispatch load, and error-propagation seam on p_token.
    #[test]
    fn idioms_recognise_transfer_shapes() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let (load_pc, _, arm_entry_slot) =
            find_dispatch_arm(&analysis.instructions, 0, ebpf::LD_B_REG, 3)
                .expect("find transfer dispatch arm");
        let func_set = function_block_set(&analysis, arm_entry_slot);
        let arm_blocks = slice_cfg(&analysis, arm_entry_slot, Some(&func_set));
        let tags = idioms::scan_arm(&analysis, &arm_blocks, Some((load_pc, 1)));

        assert!(tags
            .iter()
            .any(|i| i.pc == 198 && i.name == "read_discriminator"));
        assert!(
            tags.iter().any(|i| i.pc == 4673
                && i.name == "u64_field_decrement"
                && i.detail == "base=r5 off=72 amount=r8"),
            "transfer source debit not recognised"
        );
        assert!(
            tags.iter().any(|i| i.pc == 4676
                && i.name == "u64_field_increment"
                && i.detail == "base=r3 off=72 amount=r8"),
            "transfer dest credit not recognised"
        );
        // Concrete hit: pc 1286 `call 11385; mov64 r1,-1; jsgt r0,0`.
        assert!(
            tags.iter()
                .any(|i| i.name == "error_propagation_check"
                    && i.detail == "call_pc=1286 test_pc=1288"),
            "in-arm helper-result seam not recognised"
        );

        // Entrypoint seam: `call 12311; …; jne r0` at 59..63 — scan its block directly.
        let entry_block = analysis
            .cfg_nodes
            .values()
            .find(|b| b.instructions.start <= 59 && 59 < b.instructions.end)
            .expect("block containing the entrypoint call");
        let entry_tags = idioms::scan_arm(&analysis, &[entry_block], None);
        assert!(entry_tags.iter().any(|i| i.name == "error_propagation_check"
                && i.detail == "call_pc=59 test_pc=63"),
            "entrypoint error-propagation seam not recognised: {:?}",
            entry_tags.iter().map(|i| (i.pc, i.name)).collect::<Vec<_>>());
    }

    /// Issue #37/#41: pins the emitted transfer sidecar byte-identically (bless with
    /// QEDRECOVER_BLESS=1) and re-parses `recovered.arm_entry_pc` == 304 — closing the
    /// recover->lift handoff mechanically. Matches `transfer_arm_entry_spaces` + qedlift consumer.
    #[test]
    fn qedmeta_sidecar_emits_recovered_facts() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");
        let pc_map = PcMap::from_insns(&analysis.instructions);

        let overlay: Overlay = toml::from_str(
            &std::fs::read_to_string("../tests/fixtures/p_token.qedoverlay.toml").unwrap(),
        )
        .unwrap();
        let ovix = overlay
            .instructions
            .iter()
            .find(|o| o.name == "transfer")
            .unwrap();
        let idl_text = std::fs::read_to_string("../tests/fixtures/spl_token.codama.json").unwrap();
        let idl: Idl = serde_json::from_str(&idl_text).unwrap();
        let idl_value: serde_json::Value = serde_json::from_str(&idl_text).unwrap();
        let account_layouts = collect_account_layouts(&idl_value);
        validate_account_layout_bindings(&overlay, &idl, &account_layouts)
            .expect("overlay account layout bindings");
        let idl_ix = idl
            .program
            .instructions
            .iter()
            .find(|i| i.name == "transfer")
            .unwrap();
        let recovered = match recover_one(&analysis, &pc_map, idl_ix).expect("recover transfer") {
            Recovery::Arm(r) => r,
            Recovery::Unsupported => panic!("transfer IDL should be recoverable"),
            Recovery::DispatchMiss { .. } => panic!("transfer dispatch arm should be found"),
        };
        let trace = load_trace(Path::new("../tests/fixtures/p_token_transfer.pcs")).expect("trace");

        let mut buf: Vec<u8> = Vec::new();
        let hex = |d: &[u8]| d.iter().map(|b| format!("{:02x}", b)).collect::<String>();
        let so_sha256 = hex(&sha2::Sha256::digest(&bytes));
        let idl_sha256 = hex(&sha2::Sha256::digest(idl_text.as_bytes()));
        emit_qedmeta(
            &mut buf,
            &overlay,
            ovix,
            &idl,
            idl_ix,
            &account_layouts,
            &so_sha256,
            &idl_sha256,
            &recovered,
            Some(&trace),
        )
        .expect("emit qedmeta");
        let emitted = String::from_utf8(buf).expect("utf8");

        let fixture = "../tests/fixtures/p_token.transfer.recovered.qedmeta.toml";
        if std::env::var("QEDRECOVER_BLESS").is_ok() {
            std::fs::write(fixture, &emitted).expect("write fixture");
        }
        assert_eq!(
            emitted,
            std::fs::read_to_string(fixture).expect("read fixture"),
            "emitted qedmeta drifted from the pinned fixture \
             (regenerate with QEDRECOVER_BLESS=1)"
        );

        // Verify the consumer contract: parses through the same shape qedlift's QedMeta uses.
        #[derive(serde::Deserialize)]
        struct Field {
            name: String,
            offset: usize,
            kind: String,
        }
        #[derive(serde::Deserialize)]
        struct Layout {
            name: String,
            size: usize,
            field: Vec<Field>,
        }
        #[derive(serde::Deserialize)]
        struct Acct {
            name: String,
            layout: Option<String>,
        }
        #[derive(serde::Deserialize)]
        struct Rec {
            arm_entry_pc: usize,
            dispatch_load_pc: usize,
            dispatch_jeq_pc: usize,
        }
        #[derive(serde::Deserialize)]
        struct Ix {
            account: Vec<Acct>,
            recovered: Rec,
        }
        #[derive(serde::Deserialize)]
        struct Meta {
            schema_version: u32,
            #[serde(default)]
            account_layout: Vec<Layout>,
            #[serde(rename = "instruction")]
            instructions: Vec<Ix>,
        }
        let meta: Meta = toml::from_str(&emitted).expect("emitted sidecar must parse");
        assert_eq!(meta.schema_version, 2, "emitted schema must be v2");
        let token = meta
            .account_layout
            .iter()
            .find(|layout| layout.name == "token")
            .expect("token account layout emitted");
        assert_eq!(token.size, 165, "token layout size");
        let amount = token
            .field
            .iter()
            .find(|field| field.name == "amount")
            .expect("token amount field emitted");
        assert_eq!((amount.offset, amount.kind.as_str()), (64, "u64"));
        let rec = &meta.instructions[0].recovered;
        let source = meta.instructions[0]
            .account
            .iter()
            .find(|account| account.name == "source")
            .expect("source account emitted");
        assert_eq!(source.layout.as_deref(), Some("token"));
        let destination = meta.instructions[0]
            .account
            .iter()
            .find(|account| account.name == "destination")
            .expect("destination account emitted");
        assert_eq!(destination.layout.as_deref(), Some("token"));
        assert_eq!(
            rec.arm_entry_pc, 304,
            "emitted arm entry must be logical 304"
        );
        assert_eq!((rec.dispatch_load_pc, rec.dispatch_jeq_pc), (198, 199));
    }
}
