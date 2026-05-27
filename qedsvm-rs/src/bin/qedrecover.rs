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

// -----------------------------------------------------------------------------
// Overlay (qedsvm-specific layer over the IDL)
// -----------------------------------------------------------------------------

#[derive(Debug, Deserialize)]
struct Overlay {
    #[allow(dead_code)]
    schema_version: u32,
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
}

fn parse_args() -> Result<Args, String> {
    let mut so:      Option<PathBuf> = None;
    let mut overlay: Option<PathBuf> = None;
    let mut output:  Option<PathBuf> = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--so"      => so      = Some(it.next().ok_or("--so needs a path")?.into()),
            "--overlay" => overlay = Some(it.next().ok_or("--overlay needs a path")?.into()),
            "--output"  => output  = Some(it.next().ok_or("--output needs a path")?.into()),
            other       => return Err(format!("unknown arg: {}", other)),
        }
    }
    Ok(Args {
        so:      so.ok_or("missing --so")?,
        overlay: overlay.ok_or("missing --overlay")?,
        output,
    })
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
/// Returns `(load_pc, jump_pc, arm_entry_pc)`.
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
                    // Taken-branch arm entry = target.
                    let target = (pc as i64) + (k as i64) + 1 + (cur.off as i64);
                    return Some((pc, pc + k, target as usize));
                }
                if is_jne {
                    // Not-taken-branch arm entry = next pc.
                    return Some((pc, pc + k, pc + k + 1));
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
    disc_value: i64,
    disc_size:  usize,
    load_pc:    usize,
    jeq_pc:     usize,
    arm_entry:  usize,
    arm_blocks: &[&CfgNode],
) -> std::io::Result<()> {
    let module = format!("QedRecover.{}", pascal(&ovix.name));
    let total_insns: usize = arm_blocks.iter()
        .map(|b| b.instructions.end - b.instructions.start)
        .sum();

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
    writeln!(out, "  Happy/sad-path tagging is NOT yet applied — that requires a")?;
    writeln!(out, "  mollusk execution trace (M3c-full, separate workstream). Until")?;
    writeln!(out, "  then, `reachableBlocks` lists every block reachable from the")?;
    writeln!(out, "  arm entry within its enclosing function — both happy and sad.")?;
    writeln!(out, "-/")?;
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

    // Recovered PCs (sbpf analysis-PC space — insn slots, not byte offsets).
    writeln!(out, "/-- Recovered dispatcher site in solana-sbpf analysis-PC space.")?;
    writeln!(out, "    Note: this is an *insn-slot* index — `lddw` is 16 bytes but")?;
    writeln!(out, "    1 slot, so analysis PC ≠ byte offset / 8. -/")?;
    writeln!(out, "def dispatchLoadPc : Nat := {}", load_pc)?;
    writeln!(out, "def dispatchJeqPc  : Nat := {}", jeq_pc)?;
    writeln!(out, "def armEntryPc     : Nat := {}", arm_entry)?;
    writeln!(out)?;

    // Reachable blocks.
    writeln!(out, "/-- Reachable basic blocks from the arm entry, bounded to the")?;
    writeln!(out, "    enclosing function. Entries are `(startPc, endPc, destinations)`")?;
    writeln!(out, "    where `endPc` is exclusive and destinations are block-start PCs. -/")?;
    writeln!(out, "def reachableBlocks : List (Nat × Nat × List Nat) :=")?;
    writeln!(out, "  [")?;
    for (i, b) in arm_blocks.iter().enumerate() {
        let dests = b.destinations.iter()
            .map(|d| d.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let sep = if i + 1 < arm_blocks.len() { "," } else { "" };
        writeln!(out, "    ({}, {}, [{}]){}",
                 b.instructions.start, b.instructions.end, dests, sep)?;
    }
    writeln!(out, "  ]")?;
    writeln!(out)?;

    writeln!(out, "/-- Sanity-check totals. -/")?;
    writeln!(out, "def blockCount        : Nat := {}", arm_blocks.len())?;
    writeln!(out, "def totalInstructions : Nat := {}", total_insns)?;
    writeln!(out)?;

    writeln!(out, "end {}", module)?;

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
    #[allow(dead_code)] func_start:  usize,
    #[allow(dead_code)] func_blocks: usize,
    arm_blocks:    Vec<&'a CfgNode>,
    arm_insns:     usize,
    #[allow(dead_code)] arm_exits:   usize,
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
                func_start: usize::MAX,
                func_blocks: 0,
                arm_blocks: Vec::new(),
                arm_insns:  0,
                arm_exits:  0,
            }));
        }
    };

    let func_set    = function_block_set(analysis, arm_entry);
    let func_start  = func_set.iter().next().copied().unwrap_or(arm_entry);
    let func_blocks = func_set.len();
    let arm_blocks  = slice_cfg(analysis, arm_entry, Some(&func_set));
    let arm_insns: usize = arm_blocks.iter()
        .map(|b| b.instructions.end - b.instructions.start)
        .sum();
    let arm_exits = arm_blocks.iter()
        .filter(|b| b.destinations.is_empty()
                 || b.destinations.iter().any(|d| !func_set.contains(d)))
        .count();

    Ok(Some(Recovered {
        disc_value,
        load_pc, jeq_pc, arm_entry,
        func_start, func_blocks,
        arm_blocks, arm_insns, arm_exits,
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
                println!("  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                         idl_ix.name, r.disc_value, dpc, r.arm_entry,
                         r.arm_blocks.len(), r.arm_insns, claim);
                // Optional per-instruction extras when overlay names this
                // instruction (i.e., the project is actively claiming it):
                if ov.is_some() {
                    let _ = (r.func_start, r.func_blocks, r.arm_exits);
                    // (kept compact for now; --detail flag is the next step.)
                }
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
                // sbpf analysis-PC space ≠ disasm byte offset.
                // `lddw` is 16 bytes but 1 PC slot, so byte/8 ≠ PC.
                // We report PCs as-is and emit them downstream
                // (Lean stays in the same numbering).
                println!("    dispatch:");
                println!("      discriminator load:  pc {}", load_pc);
                println!("      jeq imm={}:           pc {}", disc_value, jeq_pc);
                println!("      → arm entry:         pc {}", arm_entry);

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

                // --- M3c-minimal: emit Lean metadata --------------------
                let disc_size = number_size(disc_format).unwrap_or(1);
                if let Some(path) = &args.output {
                    let mut f = std::fs::File::create(path)?;
                    emit_lean(&mut f, &args, &overlay, ovix, idl_ix,
                              disc_value, disc_size,
                              load_pc, jeq_pc, arm_entry, &arm_blocks)?;
                    println!();
                    println!("=== emitted Lean metadata ===");
                    println!("  output: {}", path.display());
                } else {
                    println!();
                    println!("=== Lean metadata (stdout) ===");
                    let stdout = std::io::stdout();
                    let mut lock = stdout.lock();
                    emit_lean(&mut lock, &args, &overlay, ovix, idl_ix,
                              disc_value, disc_size,
                              load_pc, jeq_pc, arm_entry, &arm_blocks)?;
                }
            }
        }
    }

    Ok(())
}
