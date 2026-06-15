//! qedrecover — recover Lean metadata for a compiled Solana program
//! from a `.so` + Codama IDL + qedsvm overlay.
//!
//! M3a (this milestone): IDL + overlay parsing + sanity dump.
//! M3b (next): dispatcher recognition → reachable CFG slice.
//! M3c (after): Lean metadata emission + ground-truth cross-check.
//!
//! Usage:
//!   cargo run --features qedrecover --bin qedrecover -- \
//!     --so       tests/fixtures/p_token.so \
//!     --overlay  tests/fixtures/p_token.qedoverlay.toml

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

use qedsvm::analysis::PcMap;
use sha2::Digest;

// -----------------------------------------------------------------------------
// Overlay (qedsvm-specific layer over the IDL)
// -----------------------------------------------------------------------------

#[derive(Debug, Deserialize)]
struct Overlay {
    idl: String,
    #[serde(rename = "instruction")]
    instructions: Vec<OverlayIx>,
}

#[derive(Debug, Deserialize)]
struct OverlayIx {
    name: String,
    // Optional: a project may name an instruction in the overlay
    // without yet making a verification claim. Recovery still runs;
    // the resulting qedmeta entry just has no claim fields.
    refines: Option<String>,
    cu_budget: Option<u64>,
}

// -----------------------------------------------------------------------------
// Codama IDL (minimal — only the fields qedrecover reads)
// -----------------------------------------------------------------------------

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
    // Opaque: Codama supports many type-node kinds (number, struct,
    // fixed-size array, …). We only special-case `numberTypeNode`
    // at use time; everything else stays as raw JSON until needed.
    #[serde(rename = "type")]
    ty: serde_json::Value,
    // Opaque for the same reason — Codama has many default-value
    // node kinds (numberValueNode, pubkeyValueNode, enumValueNode, …).
    #[serde(rename = "defaultValue", default)]
    default_value: Option<serde_json::Value>,
}

// -----------------------------------------------------------------------------
// Static-analysis context object — analysis doesn't execute.
// -----------------------------------------------------------------------------

struct NoopCtx;
impl ContextObject for NoopCtx {
    fn consume(&mut self, _amount: u64) {}
    fn get_remaining(&self) -> u64 { 0 }
}

// -----------------------------------------------------------------------------
// CLI
// -----------------------------------------------------------------------------

struct Args {
    so:      PathBuf,
    overlay: PathBuf,
    output:  Option<PathBuf>,
    /// Happy-path execution trace (`.pcs`, one decimal logical PC per
    /// line, `#` comments ignored — the format `scripts/capture_trace.sh`
    /// produces). When given, blocks containing a traced PC are tagged
    /// happy-path in the emitted metadata. Applies to the single
    /// overlay-claimed instruction; ambiguous (rejected) when the
    /// overlay claims more than one.
    trace:   Option<PathBuf>,
    /// Emit the qedmeta `.toml` sidecar (issue #37). The recovered facts
    /// qedlift consumes (`[instruction.recovered]` + idiom/tag/const-exit
    /// tables) are written here. Independent of `--output` (the
    /// `.recovered.lean`); both can be requested.
    qedmeta_out: Option<PathBuf>,
}

fn parse_args() -> Result<Args, String> {
    let mut so:      Option<PathBuf> = None;
    let mut overlay: Option<PathBuf> = None;
    let mut output:  Option<PathBuf> = None;
    let mut trace:   Option<PathBuf> = None;
    let mut qedmeta_out: Option<PathBuf> = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--so"          => so      = Some(it.next().ok_or("--so needs a path")?.into()),
            "--overlay"     => overlay = Some(it.next().ok_or("--overlay needs a path")?.into()),
            "--output"      => output  = Some(it.next().ok_or("--output needs a path")?.into()),
            "--trace"       => trace   = Some(it.next().ok_or("--trace needs a path")?.into()),
            "--qedmeta-out" => qedmeta_out = Some(it.next().ok_or("--qedmeta-out needs a path")?.into()),
            other           => return Err(format!("unknown arg: {}", other)),
        }
    }
    Ok(Args {
        so:      so.ok_or("missing --so")?,
        overlay: overlay.ok_or("missing --overlay")?,
        output,
        trace,
        qedmeta_out,
    })
}

/// Classify a constant error-exit block. Three tail shapes, all
/// "set r0 to a constant, then reach `exit` with nothing in between":
///
///   1. `…; mov64/lddw r0, imm; exit`        (exit carried in-block)
///   2. `…; mov64/lddw r0, imm; ja tgt`      where `tgt` is a bare-exit
///      block (pinocchio routes every error landing in an arm through
///      one shared `exit`)
///   3. `…; mov64/lddw r0, imm` falling through into a bare-exit block
///
/// Returns the exit code as the u64 the machine puts in r0
/// (`toU64 imm` — sign-extension wraps, matching the Lean side).
/// Each shape is collapsed in one `apply` by the matching lemma in
/// `SVM/SBPF/InstructionSpecs/Terminating.lean`:
/// `errorExit{,_lddw}_spec` (shapes 1/3) / `errorExitJa{,_lddw}_spec`
/// (shape 2).
fn error_exit_code(analysis: &Analysis, b: &CfgNode) -> Option<u64> {
    let r = &b.instructions;
    // Does the block's single destination start with a bare `exit`?
    let dest_is_exit = || -> bool {
        if b.destinations.len() != 1 { return false; }
        analysis.cfg_nodes.get(&b.destinations[0])
            .map(|d| analysis.instructions[d.instructions.start].opc == ebpf::EXIT)
            .unwrap_or(false)
    };
    if r.end == r.start { return None; }
    let last = &analysis.instructions[r.end - 1];
    // Where does the backward scan for the r0 setter begin?
    let scan_end = if last.opc == ebpf::EXIT || last.opc == ebpf::JA {
        // Exit carried in-block, or jump to a shared bare-exit block.
        if last.opc == ebpf::JA && !dest_is_exit() { return None; }
        r.end - 1
    } else {
        // Fall-through into a bare-exit block.
        if !dest_is_exit() { return None; }
        r.end
    };
    // Last write to r0 inside the block. Real error landings interleave
    // spills/cleanup between the setter and the terminator
    // (`lddw r0, c; stxdw …; ja exit`), so "the insn right before the
    // jump" is too shallow. Register-writing instruction classes are
    // LD/LDX/ALU64/ALU32 (a store's `dst` is the base register of a
    // memory write, and a compare-jump's `dst` is read-only); `call`
    // clobbers r0 with a computed value, so it ends the scan.
    for idx in (r.start..scan_end).rev() {
        let insn = &analysis.instructions[idx];
        if insn.opc == ebpf::CALL_IMM || insn.opc == ebpf::CALL_REG {
            return None; // r0 is a call result, not a constant
        }
        let class = insn.opc & 0x07;
        let writes_reg = matches!(class, 0x00 | 0x01 | 0x04 | 0x07);
        if writes_reg && insn.dst == 0 {
            return match insn.opc {
                // Analysis merges the lddw high half
                // (`augment_lddw_unchecked`), so `imm` is the full
                // 64-bit value for LD_DW_IMM.
                ebpf::MOV64_IMM | ebpf::LD_DW_IMM => Some(insn.imm as u64),
                _ => None, // r0 written, but not from a constant
            };
        }
    }
    None // r0 inherited from a predecessor block
}

/// Parse a `.pcs` trace file: one decimal logical PC per line, `#`
/// comments and blank lines ignored. Returns the PC set.
fn load_trace(path: &Path) -> Result<BTreeSet<usize>, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("--trace {}: {}", path.display(), e))?;
    let mut pcs = BTreeSet::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') { continue; }
        let pc: usize = line.parse().map_err(|_| format!(
            "--trace {}: line {}: not a decimal PC ({:?})",
            path.display(), i + 1, line))?;
        pcs.insert(pc);
    }
    if pcs.is_empty() {
        return Err(format!("--trace {}: no PCs found", path.display()));
    }
    Ok(pcs)
}

// -----------------------------------------------------------------------------
// Argument byte offsets — Codama lays out args sequentially in ix_data.
// -----------------------------------------------------------------------------

/// Size in bytes of a numeric type by Codama `format` string.
fn number_size(format: &str) -> Option<usize> {
    match format {
        "u8"  | "i8"  => Some(1),
        "u16" | "i16" => Some(2),
        "u32" | "i32" => Some(4),
        "u64" | "i64" => Some(8),
        _             => None,
    }
}

/// Map a Codama discriminator `format` to the sBPF load opcode it
/// would compile to. Only the unsigned width matters for matching.
fn discriminator_load_opc(format: &str) -> Option<u8> {
    match format {
        "u8"  => Some(ebpf::LD_B_REG),
        "u16" => Some(ebpf::LD_H_REG),
        "u32" => Some(ebpf::LD_W_REG),
        "u64" => Some(ebpf::LD_DW_REG),
        _     => None,
    }
}

/// Search the instruction stream for the dispatcher arm matching a
/// specific discriminator value. Handles two pinocchio-style shapes:
///
///   * `ldxX rD, [rS+0]; jeq rD, imm=disc, +off`
///     - branch taken (match): arm entry = target
///   * `ldxX rD, [rS+0]; jne rD, imm=disc, +off`
///     - branch NOT taken (match): arm entry = pc+1 (fall-through)
///
/// In both shapes the discriminator load and the compare-jump may be
/// adjacent (the first arm in a cluster) OR separated by other
/// compare-jumps over the SAME loaded register (subsequent arms in
/// the same dispatcher cluster, which reuse the load).
///
/// Returns `(load_pc, jump_pc, arm_entry_pc)`. PC spaces differ by
/// element: `load_pc`/`jump_pc` are indices into `instructions`
/// (logical space — lddw is one element, the numbering Lean decode,
/// qedlift, and `.pcs` traces use), while `arm_entry_pc` is a raw
/// insn-slot PC (lddw is two slots — the space `cfg_nodes` keys and
/// jump offsets live in), ready to feed `slice_cfg`. Convert with
/// `slot_to_logical` for reporting.
fn find_dispatch_arm(
    instructions: &[ebpf::Insn],
    start_pc: usize,
    load_opc: u8,
    disc_value: i64,
) -> Option<(usize, usize, usize)> {
    let n = instructions.len();
    // Walk the stream looking for any `ldxX rD, [rS+0]` (a candidate
    // discriminator load). For each candidate, scan a short window of
    // following instructions for a compare-jump on the SAME dest reg
    // with our disc value. Stop the inner scan when we hit something
    // that breaks the "dispatcher cluster" invariant (anything writing
    // the loaded register, or a non-compare-jump instruction).
    // Solana ABI puts the program input pointer in r1, so the
    // discriminator load is `ldxX r?, [r1+0]`. Restricting the source
    // register avoids matching unrelated byte/word reads at offset 0
    // of other pointers (which are common in account-parsing code).
    const INPUT_PTR_REG: u8 = 1;
    let mut pc = start_pc;
    while pc < n {
        let load = &instructions[pc];
        if load.opc != load_opc
            || load.off != 0
            || load.src != INPUT_PTR_REG
        {
            pc += 1;
            continue;
        }
        let loaded_reg = load.dst;
        // Inner scan: look up to `window` instructions ahead for the
        // matching compare-jump. The pinocchio dispatcher has all
        // arms within ~30 instructions of the load.
        let window = 64.min(n - pc - 1);
        for k in 1..=window {
            let cur = &instructions[pc + k];
            // If something writes the loaded register, the cluster ended.
            if writes_dst(cur, loaded_reg) { break; }
            // Match against our disc value.
            if cur.dst == loaded_reg && cur.imm == disc_value {
                let is_jeq = cur.opc == ebpf::JEQ32_IMM
                          || cur.opc == ebpf::JEQ64_IMM;
                let is_jne = cur.opc == ebpf::JNE32_IMM
                          || cur.opc == ebpf::JNE64_IMM;
                if is_jeq {
                    // Taken-branch arm entry = target. `off` is
                    // slot-relative, so the base must be the insn's
                    // slot (`cur.ptr`), NOT its vec index — mixing the
                    // spaces shifts the target by the number of lddw's
                    // before it (this was a real bug: p_token transfer's
                    // arm came back as 309 instead of slot 336).
                    let target = (cur.ptr as i64) + 1 + (cur.off as i64);
                    return Some((pc, pc + k, target as usize));
                }
                if is_jne {
                    // Not-taken-branch arm entry = the next slot.
                    return Some((pc, pc + k, cur.ptr + 1));
                }
            }
        }
        pc += 1;
    }
    None
}

/// True if `insn` writes the given destination register.
/// Used to detect the end of a dispatcher cluster.
fn writes_dst(insn: &ebpf::Insn, reg: u8) -> bool {
    if insn.dst != reg { return false; }
    // Anything that isn't a compare-jump on imm reads `dst` but
    // doesn't write it. ALU ops, loads, and moves write `dst`.
    let opc = insn.opc;
    // Compare-jumps: don't write dst, just read it.
    let is_cmp_jump = matches!(opc,
        ebpf::JEQ32_IMM | ebpf::JEQ64_IMM |
        ebpf::JNE32_IMM | ebpf::JNE64_IMM |
        ebpf::JGT32_IMM | ebpf::JGT64_IMM |
        ebpf::JGE32_IMM | ebpf::JGE64_IMM |
        ebpf::JLT32_IMM | ebpf::JLT64_IMM |
        ebpf::JLE32_IMM | ebpf::JLE64_IMM |
        ebpf::JSGT32_IMM | ebpf::JSGT64_IMM |
        ebpf::JSGE32_IMM | ebpf::JSGE64_IMM |
        ebpf::JSLT32_IMM | ebpf::JSLT64_IMM |
        ebpf::JSLE32_IMM | ebpf::JSLE64_IMM |
        ebpf::JSET32_IMM | ebpf::JSET64_IMM);
    !is_cmp_jump
}

/// BFS over the CFG starting at `entry`, following `destinations`
/// edges. If `bound` is `Some(set)`, only blocks whose start-PC is
/// in `set` are followed — used to constrain the walk to the entry's
/// enclosing function, so shared library helpers don't leak into the
/// arm slice.
fn slice_cfg<'a>(
    analysis: &'a Analysis<'a>,
    entry: usize,
    bound: Option<&BTreeSet<usize>>,
) -> Vec<&'a CfgNode> {
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut queue:   VecDeque<usize> = VecDeque::new();
    let mut blocks:  Vec<&CfgNode>   = Vec::new();
    queue.push_back(entry);
    while let Some(pc) = queue.pop_front() {
        if !visited.insert(pc) { continue; }
        if let Some(b) = bound { if !b.contains(&pc) { continue; } }
        if let Some(node) = analysis.cfg_nodes.get(&pc) {
            blocks.push(node);
            for &dest in &node.destinations {
                queue.push_back(dest);
            }
        }
    }
    blocks
}

/// Capitalise the first letter (cheap PascalCase for namespace names).
fn pascal(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut up = true;
    for c in s.chars() {
        if c == '_' || c == '-' { up = true; continue; }
        if up { out.extend(c.to_uppercase()); up = false; }
        else  { out.push(c); }
    }
    out
}

/// Emit recovered metadata as a Lean module.
fn emit_lean<W: std::io::Write>(
    out:        &mut W,
    args:       &Args,
    overlay:    &Overlay,
    ovix:       &OverlayIx,
    idl_ix:     &IdlInstruction,
    analysis:   &Analysis,
    pc_map:     &PcMap,
    disc_value: i64,
    disc_size:  usize,
    load_pc:    usize,
    jeq_pc:     usize,
    arm_entry_logical: usize,
    arm_blocks: &[&CfgNode],
    idiom_tags: &[idioms::Idiom],
    trace:      Option<&BTreeSet<usize>>,
) -> std::io::Result<()> {
    let module = format!("QedRecover.{}", pascal(&ovix.name));
    let total_insns: usize = arm_blocks.iter()
        .map(|b| b.instructions.end - b.instructions.start)
        .sum();
    // A block is on the happy path iff the trace executed any PC in it.
    let on_trace = |b: &CfgNode| -> bool {
        trace.is_some_and(|t|
            t.range(b.instructions.start..b.instructions.end).next().is_some())
    };

    writeln!(out, "/-")?;
    writeln!(out, "  Recovered metadata for the `{}` instruction in `{}`.",
             ovix.name, args.so.file_name().map(|s| s.to_string_lossy()).unwrap_or_default())?;
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
        writeln!(out, "  `happyPathBlocks` lists the block-start PCs the trace")?;
        writeln!(out, "  executed; the remaining `reachableBlocks` entries were not")?;
        writeln!(out, "  on the traced path (error handlers and untaken branches).")?;
    } else {
        writeln!(out, "  Happy/sad-path tagging NOT applied (no `--trace` given).")?;
        writeln!(out, "  `reachableBlocks` lists every block reachable from the arm")?;
        writeln!(out, "  entry within its enclosing function — both happy and sad.")?;
    }
    writeln!(out, "-/")?;
    writeln!(out)?;
    // Long literal lists (a correctly-rooted slice can be thousands of
    // blocks) blow Lean's default elaborator recursion depth.
    writeln!(out, "set_option maxRecDepth 65536")?;
    writeln!(out)?;
    writeln!(out, "namespace {}", module)?;
    writeln!(out)?;

    // Claim layer (overlay). `refines` / `cu_budget` are now optional;
    // emit empty / 0 sentinels when the overlay didn't claim them so
    // the generated Lean stays well-formed.
    writeln!(out, "/-- The MIR intrinsic this instruction claims to refine. -/")?;
    writeln!(out, "def refinesIntrinsic : String := \"{}\"",
             ovix.refines.as_deref().unwrap_or(""))?;
    writeln!(out)?;
    writeln!(out, "/-- CU budget claimed by the overlay. -/")?;
    writeln!(out, "def cuBudget : Nat := {}", ovix.cu_budget.unwrap_or(0))?;
    writeln!(out)?;

    // IDL-derived layout.
    writeln!(out, "/-- Account roles, in instruction-account order (from IDL). -/")?;
    writeln!(out, "def accountRoles : List String :=")?;
    writeln!(out, "  [")?;
    for (i, acc) in idl_ix.accounts.iter().enumerate() {
        let sep = if i + 1 < idl_ix.accounts.len() { "," } else { "" };
        writeln!(out, "    \"{}\"{}", acc.name, sep)?;
    }
    writeln!(out, "  ]")?;
    writeln!(out)?;

    writeln!(out, "/-- Discriminator value selecting this instruction. -/")?;
    writeln!(out, "def discriminatorValue : Nat := {}", disc_value)?;
    writeln!(out, "/-- Discriminator width in bytes (from IDL number type). -/")?;
    writeln!(out, "def discriminatorWidth : Nat := {}", disc_size)?;
    writeln!(out)?;

    // Recovered PCs (logical space: index into the decoded instruction
    // array, `lddw` = one element — the numbering Lean's
    // `Decode.decodeProgram`, qedlift, and `.pcs` traces all use).
    writeln!(out, "/-- Recovered dispatcher site, in logical PC space (decoded-array")?;
    writeln!(out, "    index, `lddw` = one element — matches Lean decode, qedlift,")?;
    writeln!(out, "    and `.pcs` trace numbering). -/")?;
    writeln!(out, "def dispatchLoadPc : Nat := {}", load_pc)?;
    writeln!(out, "def dispatchJeqPc  : Nat := {}", jeq_pc)?;
    writeln!(out, "def armEntryPc     : Nat := {}", arm_entry_logical)?;
    writeln!(out)?;

    // Reachable blocks. `CfgNode.instructions` ranges are already
    // logical; destinations are slot-space cfg keys, so convert them
    // (a key that doesn't resolve to an instruction start is emitted
    // as-is — it cannot match any block start, failing loudly).
    writeln!(out, "/-- Reachable basic blocks from the arm entry, bounded to the")?;
    writeln!(out, "    enclosing function. Entries are `(startPc, endPc, destinations)`")?;
    writeln!(out, "    where `endPc` is exclusive and destinations are block-start PCs.")?;
    writeln!(out, "    All PCs logical (same space as the other defs here). -/")?;
    writeln!(out, "def reachableBlocks : List (Nat × Nat × List Nat) :=")?;
    writeln!(out, "  [")?;
    for (i, b) in arm_blocks.iter().enumerate() {
        let dests = b.destinations.iter()
            .map(|&d| pc_map.slot_to_logical(d).unwrap_or(d).to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let sep = if i + 1 < arm_blocks.len() { "," } else { "" };
        writeln!(out, "    ({}, {}, [{}]){}",
                 b.instructions.start, b.instructions.end, dests, sep)?;
    }
    writeln!(out, "  ]")?;
    writeln!(out)?;

    // Constant-exit blocks (no trace needed — static shape).
    let const_exits: Vec<(usize, u64)> = arm_blocks.iter()
        .filter_map(|b| error_exit_code(analysis, b)
            .map(|code| (b.instructions.start, code)))
        .collect();
    writeln!(out, "/-- Blocks that exit with a CONSTANT r0 (directly, or via a jump /")?;
    writeln!(out, "    fall-through to a shared bare-`exit` block), as")?;
    writeln!(out, "    `(blockStartPc, exitCode)`. Code 0 entries are the success")?;
    writeln!(out, "    funnels; nonzero entries are constant error landings. Each is")?;
    writeln!(out, "    discharged in one `apply` of `errorExit{{,Ja}}{{,_lddw}}_spec`")?;
    writeln!(out, "    (InstructionSpecs/Terminating.lean). -/")?;
    writeln!(out, "def constExitBlocks : List (Nat × Nat) :=")?;
    writeln!(out, "  [{}]", const_exits.iter()
        .map(|(pc, code)| format!("({}, {})", pc, code))
        .collect::<Vec<_>>().join(", "))?;
    writeln!(out)?;

    // Recognised idioms (idioms.rs starter vocabulary).
    writeln!(out, "/-- Recognised instruction idioms, as `(pc, tag)` — the asm-side")?;
    writeln!(out, "    domain vocabulary. `u64_field_{{increment,decrement}}` is the")?;
    writeln!(out, "    balance-mutation triple; `error_propagation_check` marks a")?;
    writeln!(out, "    call whose r0 result is branch-tested (the compiled `Err(e)`")?;
    writeln!(out, "    propagation seam); `read_discriminator` is the dispatch load. -/")?;
    writeln!(out, "def idioms : List (Nat × String) :=")?;
    writeln!(out, "  [")?;
    for (i, idm) in idiom_tags.iter().enumerate() {
        let sep = if i + 1 < idiom_tags.len() { "," } else { "" };
        writeln!(out, "    ({}, \"{} {}\"){}", idm.pc, idm.name, idm.detail, sep)?;
    }
    writeln!(out, "  ]")?;
    writeln!(out)?;

    // Happy-path tagging (when a trace was supplied).
    if let Some(t) = trace {
        let happy: Vec<usize> = arm_blocks.iter()
            .filter(|b| on_trace(b))
            .map(|b| b.instructions.start)
            .collect();
        writeln!(out, "/-- Block-start PCs the execution trace passed through — the")?;
        writeln!(out, "    happy path of this instruction, in block order. Blocks in")?;
        writeln!(out, "    `reachableBlocks` but not here were never executed by the")?;
        writeln!(out, "    trace (error handlers / untaken branches). -/")?;
        writeln!(out, "def happyPathBlocks : List Nat :=")?;
        writeln!(out, "  [{}]", happy.iter()
            .map(|p| p.to_string()).collect::<Vec<_>>().join(", "))?;
        writeln!(out)?;
        writeln!(out, "/-- Number of PCs in the source trace. -/")?;
        writeln!(out, "def tracePcCount : Nat := {}", t.len())?;
        writeln!(out)?;
    }

    writeln!(out, "/-- Sanity-check totals. -/")?;
    writeln!(out, "def blockCount        : Nat := {}", arm_blocks.len())?;
    writeln!(out, "def totalInstructions : Nat := {}", total_insns)?;
    writeln!(out)?;

    writeln!(out, "end {}", module)?;

    Ok(())
}

/// Emit the qedmeta `.toml` sidecar from the recovered facts (issue #37 /
/// #41 producer half). Previously qedrecover only rendered the Lean
/// metadata; the `qedmeta.toml` was hand-shaped. Now the SAME facts are
/// written into the sidecar qedlift consumes (`[instruction.recovered]
/// .arm_entry_pc` etc.), so the recover→lift handoff is mechanical, not
/// hand-authored. Schema v2 (qedmeta/0.2): the `recovered`/`idiom`/`tag`
/// tables are populated. The `[instruction.proofs]` binding is NOT
/// emitted — it links to a Lean theorem, a human/qedgen assertion the
/// recogniser doesn't know.
///
/// All PCs written are LOGICAL (decoded-array indices), the space qedlift
/// and `.pcs` traces use — `CfgNode.instructions` ranges are already
/// logical; the dispatch/arm/func PCs are converted by the caller.
#[allow(clippy::too_many_arguments)]
fn emit_qedmeta<W: std::io::Write>(
    out:        &mut W,
    overlay:    &Overlay,
    ovix:       &OverlayIx,
    idl:        &Idl,
    idl_ix:     &IdlInstruction,
    analysis:   &Analysis,
    so_sha256:  &str,
    idl_sha256: &str,
    disc_value: i64,
    disc_size:  usize,
    disc_format:&str,
    load_pc:    usize,
    jeq_pc:     usize,
    arm_entry_logical:      usize,
    enclosing_func_logical: usize,
    arm_blocks: &[&CfgNode],
    idiom_tags: &[idioms::Idiom],
    trace:      Option<&BTreeSet<usize>>,
) -> std::io::Result<()> {
    writeln!(out, "# qedmeta sidecar — emitted by qedrecover (do not edit by hand).")?;
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
    writeln!(out, "value       = {}", disc_value)?;
    writeln!(out, "width_bytes = {}", disc_size)?;
    writeln!(out, "format      = \"{}\"", disc_format)?;
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
    }
    writeln!(out)?;

    // ----- recovered facts (the section qedlift Phase 4 consumes) -----
    let total_insns: usize = arm_blocks.iter()
        .map(|b| b.instructions.end - b.instructions.start)
        .sum();
    writeln!(out, "[instruction.recovered]")?;
    writeln!(out, "dispatch_load_pc   = {}", load_pc)?;
    writeln!(out, "dispatch_jeq_pc    = {}", jeq_pc)?;
    writeln!(out, "arm_entry_pc       = {}", arm_entry_logical)?;
    writeln!(out, "enclosing_func_pc  = {}", enclosing_func_logical)?;
    writeln!(out, "block_count        = {}", arm_blocks.len())?;
    writeln!(out, "total_instructions = {}", total_insns)?;
    // The full `blocks` CFG slice is elided here (1940 rows on p_token);
    // qedlift consumes `arm_entry_pc`, not the slice. The `.recovered.lean`
    // (--output) carries the full `reachableBlocks` for inspection.
    writeln!(out, "blocks = []")?;
    writeln!(out)?;

    // ----- idiom tags (v0.2) -----
    for idm in idiom_tags {
        writeln!(out, "[[instruction.idiom]]")?;
        writeln!(out, "pc      = {}", idm.pc)?;
        writeln!(out, "pattern = \"{}\"", idm.name)?;
        writeln!(out, "detail  = \"{}\"", idm.detail)?;
    }
    if !idiom_tags.is_empty() { writeln!(out)?; }

    // ----- constant-exit blocks (v0.2): static `r0 := const; exit` -----
    for b in arm_blocks {
        if let Some(code) = error_exit_code(analysis, b) {
            writeln!(out, "[[instruction.const_exit]]")?;
            writeln!(out, "block_start = {}", b.instructions.start)?;
            writeln!(out, "exit_code   = {}", code)?;
            writeln!(out, "role        = \"{}\"",
                     if code == 0 { "success" } else { "error" })?;
        }
    }

    // ----- happy-path tags (v0.2): only with a --trace -----
    if let Some(t) = trace {
        for b in arm_blocks {
            if t.range(b.instructions.start..b.instructions.end).next().is_some() {
                writeln!(out, "[[instruction.tag]]")?;
                writeln!(out, "block_start = {}", b.instructions.start)?;
                writeln!(out, "role        = \"happy\"")?;
            }
        }
    }

    Ok(())
}

/// Set of basic-block start PCs that lie within the function
/// containing `entry`. Uses `analysis.functions` (BTreeMap keyed by
/// function start) to find the enclosing function's PC range, then
/// collects every `cfg_nodes` key that falls inside.
fn function_block_set(analysis: &Analysis, entry: usize) -> BTreeSet<usize> {
    let func_start = analysis.functions.range(..=entry)
        .next_back()
        .map(|(&k, _)| k)
        .unwrap_or(0);
    let func_end = analysis.functions.range((std::ops::Bound::Excluded(func_start),
                                             std::ops::Bound::Unbounded))
        .next()
        .map(|(&k, _)| k)
        .unwrap_or(analysis.instructions.len());
    analysis.cfg_nodes.range(func_start..func_end)
        .map(|(&k, _)| k)
        .collect()
}

// -----------------------------------------------------------------------------
// Per-instruction recovery
// -----------------------------------------------------------------------------

/// Outcome of trying to recover one IDL instruction from the binary.
/// `None` means recovery couldn't proceed (e.g., no numeric discriminator
/// or an unsupported arg type); `Some` means dispatcher recognition and
/// CFG slicing produced a result, even if the slice is empty.
struct Recovered<'a> {
    disc_value:    i64,
    load_pc:       usize,
    jeq_pc:        usize,
    arm_entry:     usize,
    arm_blocks:    Vec<&'a CfgNode>,
    arm_insns:     usize,
}

/// Run dispatcher recognition + CFG slicing on one IDL instruction.
/// Returns `Ok(None)` for instructions whose IDL shape qedrecover
/// can't analyse (non-numeric args, unsupported widths) — the caller
/// reports them as "skipped" rather than failures.
fn recover_one<'a>(
    analysis: &'a Analysis<'a>,
    idl_ix:   &'a IdlInstruction,
) -> Result<Option<Recovered<'a>>, String> {
    // Find the discriminator arg (by name) and pull its width + value.
    // Other args can have any shape (struct, fixed-size array, ...) —
    // we don't need them for dispatcher recognition.
    let disc_arg = match idl_ix.arguments.iter().find(|a| a.name == "discriminator") {
        Some(a) => a,
        None    => return Ok(None),   // no discriminator arg in IDL
    };
    let disc_format = match disc_arg.ty.get("format").and_then(|v| v.as_str()) {
        Some(f) => f,
        None    => return Ok(None),   // discriminator isn't a number-typed node
    };
    let disc_value = match disc_arg.default_value.as_ref()
        .and_then(|d| d.get("number"))
        .and_then(|n| n.as_i64())
    {
        Some(v) => v,
        None    => return Ok(None),   // no fixed discriminator value (variable arg)
    };
    let load_opc = match discriminator_load_opc(disc_format) {
        Some(opc) => opc,
        None      => return Ok(None), // unsupported width
    };

    // Search the bytecode for the dispatcher pair.
    let (load_pc, jeq_pc, arm_entry) = match find_dispatch_arm(
        &analysis.instructions, 0, load_opc, disc_value,
    ) {
        Some(t) => t,
        None    => {
            // Dispatch not found in binary — return Recovered with empty
            // arm_blocks so the caller can report it consistently.
            return Ok(Some(Recovered {
                disc_value,
                load_pc:    usize::MAX,
                jeq_pc:     usize::MAX,
                arm_entry:  usize::MAX,
                arm_blocks: Vec::new(),
                arm_insns:  0,
            }));
        }
    };

    let func_set    = function_block_set(analysis, arm_entry);
    let arm_blocks  = slice_cfg(analysis, arm_entry, Some(&func_set));
    let arm_insns: usize = arm_blocks.iter()
        .map(|b| b.instructions.end - b.instructions.start)
        .sum();

    Ok(Some(Recovered {
        disc_value,
        load_pc, jeq_pc, arm_entry,
        arm_blocks, arm_insns,
    }))
}

// -----------------------------------------------------------------------------
// Main
// -----------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = parse_args().map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

    // 1. Overlay.
    let overlay_text = std::fs::read_to_string(&args.overlay)?;
    let overlay: Overlay = toml::from_str(&overlay_text)?;
    let overlay_by_name: std::collections::BTreeMap<&str, &OverlayIx> =
        overlay.instructions.iter().map(|ix| (ix.name.as_str(), ix)).collect();

    // 2. IDL — path is relative to the overlay file.
    let overlay_dir: &Path = args.overlay.parent().unwrap_or(Path::new("."));
    let idl_path = overlay_dir.join(&overlay.idl);
    let idl_text = std::fs::read_to_string(&idl_path)?;
    let idl: Idl = serde_json::from_str(&idl_text)?;

    // 3. ELF + static analysis.
    let bytes = std::fs::read(&args.so)?;
    let loader = Arc::new(BuiltinProgram::new_mock());
    let executable: Executable<NoopCtx> = Executable::load(&bytes, loader)?;
    let analysis = Analysis::from_executable(&executable)?;
    // One slot<->logical converter, shared with qedlift. Derived from
    // the decoded insn list; `pc_map_matches_analysis_ptrs` pins that it
    // agrees with `analysis.instructions[].ptr` (issue #41).
    let pc_map = PcMap::from_insns(&analysis.instructions);

    // 4. Sanity dump.
    println!("=== inputs ===");
    println!("  .so:     {}", args.so.display());
    println!("  overlay: {}", args.overlay.display());
    println!("  idl:     {} (program {} @ {})",
             idl_path.display(), idl.program.name, idl.program.public_key);
    println!();

    println!("=== ELF analysis ===");
    println!("  entrypoint:   pc 0x{:x}", analysis.entrypoint);
    println!("  instructions: {}", analysis.instructions.len());
    println!("  basic blocks: {}", analysis.cfg_nodes.len());
    println!("  functions:    {}", analysis.functions.len());
    println!();

    // 5. Whole-program scan: iterate IDL, recover each instruction,
    //    print a compact summary line. Overlay claims (where present)
    //    decorate the line; their absence does NOT skip recovery.
    println!("=== whole-program recovery ===");
    println!("  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
             "instruction", "disc", "dispatch (pc)", "armPc", "blks", "insns", "claim");
    println!("  {}", "-".repeat(96));

    let mut total          = 0usize;
    let mut recovered_ok   = 0usize;
    let mut dispatch_miss  = 0usize;
    let mut idl_unsupp     = 0usize;

    for idl_ix in &idl.program.instructions {
        total += 1;
        let ov = overlay_by_name.get(idl_ix.name.as_str()).copied();
        let claim = match ov {
            Some(o) => {
                let refines = o.refines.as_deref().unwrap_or("?");
                let cu      = o.cu_budget.map(|c| format!("CU={}", c))
                                         .unwrap_or_default();
                format!("{} {}", refines, cu).trim().to_string()
            }
            None => String::new(),
        };

        match recover_one(&analysis, idl_ix)? {
            None => {
                idl_unsupp += 1;
                println!("  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                         idl_ix.name, "—", "skip (idl)", "—", "—", "—", claim);
            }
            Some(r) if r.arm_blocks.is_empty() => {
                dispatch_miss += 1;
                let dpc = if r.load_pc == usize::MAX {
                    "not found".to_string()
                } else { format!("{}/{}", r.load_pc, r.jeq_pc) };
                println!("  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                         idl_ix.name, r.disc_value, dpc, "—", "—", "—", claim);
            }
            Some(r) => {
                recovered_ok += 1;
                let dpc = format!("{}/{}", r.load_pc, r.jeq_pc);
                let arm_logical = pc_map.slot_to_logical(r.arm_entry)
                    .unwrap_or(r.arm_entry);
                println!("  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                         idl_ix.name, r.disc_value, dpc, arm_logical,
                         r.arm_blocks.len(), r.arm_insns, claim);
            }
        }
    }

    println!("  {}", "-".repeat(96));
    println!("  recovered: {}/{}   dispatch-miss: {}   idl-skipped: {}",
             recovered_ok, total, dispatch_miss, idl_unsupp);
    if recovered_ok < total {
        println!();
        println!("  legend:");
        println!("    skip (idl)    — IDL shape qedrecover can't analyse yet (non-number arg, etc.)");
        println!("    not found     — IDL shape OK but no `ldx + jeq imm=<disc>` pair in the binary");
    }
    println!();

    // 6. Optional detailed pass — kept compatible with the prior
    //    behaviour: any instruction NAMED in the overlay with a
    //    `refines` claim still gets the verbose printout + Lean
    //    metadata emit. Multi-instruction Lean emission is gated on
    //    --output being a directory; not implemented yet.
    let claimed: Vec<&OverlayIx> = overlay.instructions.iter()
        .filter(|o| o.refines.is_some())
        .collect();
    let trace_pcs = match args.trace.as_ref() {
        Some(p) => {
            if claimed.len() != 1 {
                return Err(format!(
                    "--trace is per-instruction but the overlay claims {} \
                     instructions; narrow the overlay to one",
                    claimed.len()).into());
            }
            // Trace PCs are logical indices — the same space as
            // `CfgNode.instructions` ranges, so tagging compares
            // directly (no slot conversion).
            Some(load_trace(p)?)
        }
        None => None,
    };
    if !claimed.is_empty() {
        println!("=== detailed view (overlay-claimed) ===");
    }
    for ovix in claimed {
        let idl_ix = idl.program.instructions.iter()
            .find(|i| i.name == ovix.name)
            .ok_or_else(|| format!(
                "overlay names instruction `{}` but IDL has no such instruction",
                ovix.name))?;

        println!("  instruction: {}", ovix.name);
        println!("    refines:    {}", ovix.refines.as_deref().unwrap_or("—"));
        println!("    cu_budget:  {}", ovix.cu_budget
                                          .map(|c| c.to_string())
                                          .unwrap_or_else(|| "—".to_string()));

        // Argument byte offsets (Codama lays them out sequentially).
        // Only numberTypeNode args have a fixed byte size we can use;
        // anything else aborts (the spike doesn't claim to cover them).
        let mut off: usize = 0;
        let mut disc_value: Option<i64> = None;
        println!("    ix_data:");
        for arg in &idl_ix.arguments {
            let kind   = arg.ty.get("kind")  .and_then(|v| v.as_str()).unwrap_or("?");
            let format = arg.ty.get("format").and_then(|v| v.as_str())
                .ok_or_else(|| format!("arg `{}` has non-number type ({}), unsupported in spike",
                                       arg.name, kind))?;
            let sz = number_size(format)
                .ok_or_else(|| format!("unsupported number format: {}", format))?;
            // numberValueNode carries the literal under "number";
            // other default-value node kinds are skipped silently.
            let default = arg.default_value.as_ref()
                .and_then(|d| d.get("number"))
                .and_then(|n| n.as_i64());
            if arg.name == "discriminator" {
                disc_value = default;
            }
            let default_str = default.map(|n| format!(" = {}", n)).unwrap_or_default();
            println!("      [{:#x}..{:#x}] {} : {}{}",
                     off, off + sz, arg.name, format, default_str);
            off += sz;
        }

        // Discriminator summary — qedrecover's downstream dispatcher
        // recogniser needs (kind, value) to know what byte pattern
        // to search for from the entry point.
        if let Some(v) = disc_value {
            println!("    discriminator: u8 = {} (looks for `ldxb`/`ldxw` + `jeq imm = {}`)",
                     v, v);
        }

        // Account layout: index → role.
        println!("    accounts:");
        for (i, acc) in idl_ix.accounts.iter().enumerate() {
            let signer = match &acc.is_signer {
                serde_json::Value::Bool(b) => if *b { "signer" } else { "—" },
                serde_json::Value::String(s) if s == "either" => "signer?",
                _ => "—",
            };
            let writ = if acc.is_writable { "writable" } else { "ro" };
            println!("      [{}] {:14} {} {}", i, acc.name, writ, signer);
        }

        // --- M3b: dispatcher recognition --------------------------------
        let Some(disc_value) = disc_value else {
            println!("    [skip recognition: no numeric discriminator value]");
            continue;
        };
        let first_arg = &idl_ix.arguments[0];
        let disc_format = first_arg.ty.get("format").and_then(|v| v.as_str())
            .ok_or("discriminator arg has no numeric format")?;
        let load_opc = discriminator_load_opc(disc_format)
            .ok_or_else(|| format!("unsupported disc width: {}", disc_format))?;

        // Scan whole instruction stream. sbpf's analysis PC space
        // doesn't follow control-flow order — the dispatcher can sit
        // at a lower PC than `entrypoint` due to linker layout
        // (verified empirically: pinocchio's transfer dispatcher
        // lives at PC 198 while entrypoint reports PC 225). Whole-
        // stream scan + uniqueness-by-discriminator-value is the
        // simplest sound recovery for the spike.
        match find_dispatch_arm(
            &analysis.instructions,
            0,
            load_opc,
            disc_value,
        ) {
            None => {
                println!("    dispatch:    NOT FOUND \
                          (no `{}` + `jeq imm={}` pair from entry)",
                         disc_format, disc_value);
            }
            Some((load_pc, jeq_pc, arm_entry)) => {
                // `load_pc`/`jeq_pc` are logical (decoded-array index);
                // `arm_entry` is a slot PC (the space cfg_nodes/slicing
                // use). Report the logical arm entry alongside.
                let arm_entry_logical = pc_map.slot_to_logical(arm_entry)
                    .unwrap_or(arm_entry);
                println!("    dispatch:");
                println!("      discriminator load:  pc {}", load_pc);
                println!("      jeq imm={}:           pc {}", disc_value, jeq_pc);
                println!("      → arm entry:         pc {} (slot {})",
                         arm_entry_logical, arm_entry);

                // Constrain the slice to the enclosing function so
                // shared library helpers (account parsing, codec
                // routines reachable via `call`) don't leak in.
                let func_set = function_block_set(&analysis, arm_entry);
                let func_start = func_set.iter().next().copied().unwrap_or(arm_entry);
                println!("      enclosing function: pc {} ({} blocks)",
                         func_start, func_set.len());

                let arm_blocks = slice_cfg(&analysis, arm_entry, Some(&func_set));
                let total_insns: usize = arm_blocks.iter()
                    .map(|b| b.instructions.end - b.instructions.start)
                    .sum();
                let unconstrained = slice_cfg(&analysis, arm_entry, None);
                println!("    arm slice (function-bounded):");
                println!("      basic blocks: {} (unconstrained: {})",
                         arm_blocks.len(), unconstrained.len());
                println!("      instructions: {}", total_insns);

                // Sample exit edges. Two kinds matter for happy/sad
                // tagging downstream (M3c): blocks that exit the
                // function (return/exit/unreachable) and blocks that
                // branch within the function. The first kind likely
                // includes the error-handler landings — the landmark
                // M3c needs.
                let exiting: Vec<&CfgNode> = arm_blocks.iter()
                    .filter(|b| b.destinations.is_empty()
                             || b.destinations.iter().any(|d| !func_set.contains(d)))
                    .copied()
                    .collect();
                println!("      blocks with exits outside the function: {}",
                         exiting.len());

                // --- idiom recognition -----------------------------------
                let idiom_tags = idioms::scan_arm(
                    &analysis, &arm_blocks,
                    Some((load_pc, number_size(disc_format).unwrap_or(1))));
                {
                    let mut counts: std::collections::BTreeMap<&str, usize> =
                        std::collections::BTreeMap::new();
                    for idm in &idiom_tags {
                        *counts.entry(idm.name).or_default() += 1;
                    }
                    let rendered = counts.iter()
                        .map(|(n, c)| format!("{} x{}", n, c))
                        .collect::<Vec<_>>().join(", ");
                    println!("      idioms: {}",
                             if rendered.is_empty() { "none".to_string() }
                             else { rendered });
                }

                // --- constant-exit blocks (static shape) ----------------
                let (n_zero, n_nonzero) = arm_blocks.iter()
                    .filter_map(|b| error_exit_code(&analysis, b))
                    .fold((0usize, 0usize), |(z, nz), code|
                        if code == 0 { (z + 1, nz) } else { (z, nz + 1) });
                println!("      constant-exit blocks: {} success (code 0), {} error",
                         n_zero, n_nonzero);

                // --- happy-path tagging (when --trace given) ------------
                if let Some(t) = trace_pcs.as_ref() {
                    let happy = arm_blocks.iter()
                        .filter(|b| t.range(b.instructions.start..b.instructions.end)
                                     .next().is_some())
                        .count();
                    println!("      happy-path blocks (on trace): {}/{} ({} traced PCs)",
                             happy, arm_blocks.len(), t.len());
                }

                // --- M3c-minimal: emit Lean metadata --------------------
                let disc_size = number_size(disc_format).unwrap_or(1);
                if let Some(path) = &args.output {
                    let mut f = std::fs::File::create(path)?;
                    emit_lean(&mut f, &args, &overlay, ovix, idl_ix,
                              &analysis, &pc_map, disc_value, disc_size,
                              load_pc, jeq_pc, arm_entry_logical, &arm_blocks,
                              &idiom_tags, trace_pcs.as_ref())?;
                    println!();
                    println!("=== emitted Lean metadata ===");
                    println!("  output: {}", path.display());
                } else {
                    println!();
                    println!("=== Lean metadata (stdout) ===");
                    let stdout = std::io::stdout();
                    let mut lock = stdout.lock();
                    emit_lean(&mut lock, &args, &overlay, ovix, idl_ix,
                              &analysis, &pc_map, disc_value, disc_size,
                              load_pc, jeq_pc, arm_entry_logical, &arm_blocks,
                              &idiom_tags, trace_pcs.as_ref())?;
                }

                // qedmeta sidecar (issue #37): write the recovered facts
                // qedlift consumes, so the recover→lift handoff is
                // mechanical (not a hand-shaped fixture). Independent of
                // --output (the `.recovered.lean`); both may be requested.
                if let Some(meta_path) = &args.qedmeta_out {
                    let enclosing_func_logical =
                        pc_map.slot_to_logical(func_start).unwrap_or(func_start);
                    let hex = |d: &[u8]| d.iter()
                        .map(|b| format!("{:02x}", b)).collect::<String>();
                    let so_sha256  = hex(&sha2::Sha256::digest(&bytes));
                    let idl_sha256 = hex(&sha2::Sha256::digest(idl_text.as_bytes()));
                    let mut f = std::fs::File::create(meta_path)?;
                    emit_qedmeta(&mut f, &overlay, ovix, &idl, idl_ix, &analysis,
                        &so_sha256, &idl_sha256, disc_value, disc_size, disc_format,
                        load_pc, jeq_pc, arm_entry_logical, enclosing_func_logical,
                        &arm_blocks, &idiom_tags, trace_pcs.as_ref())?;
                    println!();
                    println!("=== emitted qedmeta sidecar ===");
                    println!("  output: {}", meta_path.display());
                }
            }
        }
    }

    Ok(())
}

// -----------------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Pins the PC-space discipline of dispatcher recovery on the real
    /// p_token binary. `find_dispatch_arm` must compute the arm-entry
    /// jump target in SLOT space (insn.ptr + 1 + off) — computing it
    /// from the vec index was a real bug that put transfer's arm at
    /// 309 (mid-dispatcher code) instead of slot 336 / logical 304,
    /// rooting the CFG slice at the wrong block. Logical 304 is
    /// ground truth: the captured execution trace
    /// (tests/fixtures/p_token_transfer.pcs) jumps 199 -> 304.
    #[test]
    fn transfer_arm_entry_spaces() {
        let bytes = std::fs::read("tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let (load_pc, jeq_pc, arm_entry_slot) = find_dispatch_arm(
            &analysis.instructions, 0, ebpf::LD_B_REG, 3,
        ).expect("find transfer dispatch arm");

        assert_eq!((load_pc, jeq_pc), (198, 199), "dispatcher site moved");
        assert_eq!(arm_entry_slot, 336, "arm entry must be a slot PC");
        let pc_map = PcMap::from_insns(&analysis.instructions);
        assert_eq!(pc_map.slot_to_logical(arm_entry_slot), Some(304),
            "slot 336 must resolve to logical 304 (the PC the trace jumps to)");

        // The slice rooted at the slot entry must contain the blocks the
        // happy-path trace executes (in logical space).
        let func_set = function_block_set(&analysis, arm_entry_slot);
        let arm_blocks = slice_cfg(&analysis, arm_entry_slot, Some(&func_set));
        let trace = load_trace(Path::new("tests/fixtures/p_token_transfer.pcs"))
            .expect("load transfer trace");
        let happy = arm_blocks.iter()
            .filter(|b| trace.range(b.instructions.start..b.instructions.end)
                         .next().is_some())
            .count();
        assert_eq!(happy, 27,
            "happy-path tagging drifted: expected 27 on-trace blocks, got {}", happy);

        // Constant-exit classification inside the arm slice: p_token's
        // transfer errors return COMPUTED r0 through call boundaries, so
        // the only constant-exit blocks are the nine r0=0 success
        // funnels (`mov64 r0, 0; … ; ja <shared exit>`). A nonzero hit
        // here would mean the detector started tagging computed codes.
        let codes: Vec<u64> = arm_blocks.iter()
            .filter_map(|b| error_exit_code(&analysis, b))
            .collect();
        assert_eq!(codes.len(), 9, "constant-exit block count drifted");
        assert!(codes.iter().all(|&c| c == 0),
            "transfer arm has no constant nonzero exits; got {:?}", codes);
    }

    /// Pins the issue-#41 invariant that the shared `PcMap` (built from
    /// the decoded insn list) agrees with sbpf's own `analysis
    /// .instructions[].ptr` numbering on the real p_token binary — the
    /// equivalence that lets qedrecover swap its former
    /// `binary_search`-over-`.ptr` `slot_to_logical` for the shared
    /// converter byte-identically. Checks the full round trip in both
    /// directions over every instruction.
    #[test]
    fn pc_map_matches_analysis_ptrs() {
        let bytes = std::fs::read("tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let pc_map = PcMap::from_insns(&analysis.instructions);
        assert_eq!(pc_map.logical_len(), analysis.instructions.len(),
            "shared PcMap covers a different instruction count than analysis");
        for (logical, insn) in analysis.instructions.iter().enumerate() {
            // logical -> slot agrees with sbpf's recorded ptr.
            assert_eq!(pc_map.logical_to_slot(logical), Some(insn.ptr),
                "logical {} maps to a different slot than analysis .ptr", logical);
            // slot -> logical inverts it (matches the old binary_search result).
            assert_eq!(pc_map.slot_to_logical(insn.ptr), Some(logical),
                "slot {} (logical {}) failed to round-trip", insn.ptr, logical);
        }
    }

    /// The constant ERROR landings live in the entrypoint prelude:
    /// shape 1 (`lddw r0, 19<<32; exit` — the dispatch-mismatch exit at
    /// logical 196..198) and shape 2 (`lddw r0, 10<<32; ja <bare exit>`
    /// at logical 124..126). Pins `error_exit_code` against both real
    /// shapes, codes included.
    #[test]
    fn entrypoint_error_landings_classify() {
        let bytes = std::fs::read("tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let block_containing = |logical: usize| -> &CfgNode {
            analysis.cfg_nodes.values()
                .find(|b| b.instructions.start <= logical && logical < b.instructions.end)
                .expect("block containing pc")
        };
        // Shape 1: dispatch-mismatch `lddw r0, 19<<32; exit`.
        assert_eq!(error_exit_code(&analysis, block_containing(196)),
            Some(19u64 << 32), "dispatch-mismatch landing misclassified");
        // Shape 2: prelude landing `lddw r0, 10<<32; ja <bare exit>`.
        assert_eq!(error_exit_code(&analysis, block_containing(124)),
            Some(10u64 << 32), "prelude ja-landing misclassified");
    }

    /// Idiom recogniser pins on real p_token bytecode.
    #[test]
    fn idioms_recognise_transfer_shapes() {
        let bytes = std::fs::read("tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        // Arm slice idioms: the transfer debit/credit pair must be
        // recognised as a u64_field_decrement/increment on the same
        // offset, and the dispatch load as read_discriminator.
        let (load_pc, _, arm_entry_slot) = find_dispatch_arm(
            &analysis.instructions, 0, ebpf::LD_B_REG, 3,
        ).expect("find transfer dispatch arm");
        let func_set = function_block_set(&analysis, arm_entry_slot);
        let arm_blocks = slice_cfg(&analysis, arm_entry_slot, Some(&func_set));
        let tags = idioms::scan_arm(&analysis, &arm_blocks, Some((load_pc, 1)));

        assert!(tags.iter().any(|i| i.pc == 198 && i.name == "read_discriminator"));
        assert!(tags.iter().any(|i| i.pc == 4673
                && i.name == "u64_field_decrement"
                && i.detail == "base=r5 off=72 amount=r8"),
            "transfer source debit not recognised");
        assert!(tags.iter().any(|i| i.pc == 4676
                && i.name == "u64_field_increment"
                && i.detail == "base=r3 off=72 amount=r8"),
            "transfer dest credit not recognised");
        // In-arm propagation seams: helper calls whose r0 result is
        // branch-tested in the fall-through block (a call always ends
        // its block). e.g. pc 1286: `call 11385; mov64 r1, -1;
        // jsgt r0, 0` — pin one concrete hit.
        assert!(tags.iter().any(|i| i.name == "error_propagation_check"
                && i.detail == "call_pc=1286 test_pc=1288"),
            "in-arm helper-result seam not recognised");

        // The real propagation seam is the entrypoint's
        // `call 12311; …; jne r0` at 59..63 — scan its block directly.
        let entry_block = analysis.cfg_nodes.values()
            .find(|b| b.instructions.start <= 59 && 59 < b.instructions.end)
            .expect("block containing the entrypoint call");
        let entry_tags = idioms::scan_arm(&analysis, &[entry_block], None);
        assert!(entry_tags.iter().any(|i| i.name == "error_propagation_check"
                && i.detail == "call_pc=59 test_pc=63"),
            "entrypoint error-propagation seam not recognised: {:?}",
            entry_tags.iter().map(|i| (i.pc, i.name)).collect::<Vec<_>>());
    }

    /// Issue #37 / #41 producer half: qedrecover EMITS the qedmeta sidecar
    /// (it used to only render Lean metadata; the `.toml` was hand-shaped).
    /// Pins the emitted transfer sidecar byte-identically (regenerate with
    /// QEDRECOVER_BLESS=1) AND re-parses it through the SAME
    /// `recovered.arm_entry_pc` shape qedlift consumes — closing the
    /// recover→lift handoff loop mechanically rather than via the
    /// hand-authored fixture. `arm_entry_pc` must be logical 304, matching
    /// the `transfer_arm_entry_spaces` pin and qedlift's consumer pin.
    #[test]
    fn qedmeta_sidecar_emits_recovered_facts() {
        let bytes = std::fs::read("tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");
        let pc_map = PcMap::from_insns(&analysis.instructions);

        // Drive the same recovery `main` runs for transfer (disc=3, u8 load).
        let (load_pc, jeq_pc, arm_entry_slot) = find_dispatch_arm(
            &analysis.instructions, 0, ebpf::LD_B_REG, 3).expect("dispatch arm");
        let arm_entry_logical = pc_map.slot_to_logical(arm_entry_slot).expect("arm logical");
        let func_set = function_block_set(&analysis, arm_entry_slot);
        let func_start = func_set.iter().next().copied().unwrap_or(arm_entry_slot);
        let enclosing_func_logical = pc_map.slot_to_logical(func_start).unwrap_or(func_start);
        let arm_blocks = slice_cfg(&analysis, arm_entry_slot, Some(&func_set));
        let idiom_tags = idioms::scan_arm(&analysis, &arm_blocks, Some((load_pc, 1)));
        let trace = load_trace(Path::new("tests/fixtures/p_token_transfer.pcs")).expect("trace");

        // Real overlay + IDL so [target]/[idl]/account rendering is exercised.
        let overlay: Overlay = toml::from_str(
            &std::fs::read_to_string("tests/fixtures/p_token.qedoverlay.toml").unwrap()).unwrap();
        let ovix = overlay.instructions.iter().find(|o| o.name == "transfer").unwrap();
        let idl_text = std::fs::read_to_string("tests/fixtures/spl_token.codama.json").unwrap();
        let idl: Idl = serde_json::from_str(&idl_text).unwrap();
        let idl_ix = idl.program.instructions.iter().find(|i| i.name == "transfer").unwrap();

        let mut buf: Vec<u8> = Vec::new();
        // Real SHA-256 of the .so/IDL the sidecar hash-pins.
        let hex = |d: &[u8]| d.iter().map(|b| format!("{:02x}", b)).collect::<String>();
        let so_sha256  = hex(&sha2::Sha256::digest(&bytes));
        let idl_sha256 = hex(&sha2::Sha256::digest(idl_text.as_bytes()));
        emit_qedmeta(&mut buf, &overlay, ovix, &idl, idl_ix, &analysis,
            &so_sha256, &idl_sha256, 3, 1, "u8",
            load_pc, jeq_pc, arm_entry_logical, enclosing_func_logical,
            &arm_blocks, &idiom_tags, Some(&trace)).expect("emit qedmeta");
        let emitted = String::from_utf8(buf).expect("utf8");

        // Byte-identical pin against the committed emitted fixture.
        let fixture = "tests/fixtures/p_token.transfer.recovered.qedmeta.toml";
        if std::env::var("QEDRECOVER_BLESS").is_ok() {
            std::fs::write(fixture, &emitted).expect("write fixture");
        }
        assert_eq!(emitted, std::fs::read_to_string(fixture).expect("read fixture"),
            "emitted qedmeta drifted from the pinned fixture \
             (regenerate with QEDRECOVER_BLESS=1)");

        // Consumer contract: the emitted sidecar parses through the same
        // `recovered.arm_entry_pc` shape qedlift's QedMeta uses, == 304.
        #[derive(serde::Deserialize)]
        struct Rec { arm_entry_pc: usize, dispatch_load_pc: usize, dispatch_jeq_pc: usize }
        #[derive(serde::Deserialize)]
        struct Ix { recovered: Rec }
        #[derive(serde::Deserialize)]
        struct Meta { schema_version: u32,
                      #[serde(rename = "instruction")] instructions: Vec<Ix> }
        let meta: Meta = toml::from_str(&emitted).expect("emitted sidecar must parse");
        assert_eq!(meta.schema_version, 2, "emitted schema must be v2");
        let rec = &meta.instructions[0].recovered;
        assert_eq!(rec.arm_entry_pc, 304, "emitted arm entry must be logical 304");
        assert_eq!((rec.dispatch_load_pc, rec.dispatch_jeq_pc), (198, 199));
    }
}
