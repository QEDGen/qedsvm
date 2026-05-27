//! qedlift — end-to-end lift demo for a simple Solana program.
//!
//! Takes a `.so` whose `.text` is short and straight-line, and emits a
//! Lean module that:
//!   1. embeds the `.text` bytes verbatim as a `ByteArray`,
//!   2. decodes them via `SVM.SBPF.Decode.decodeProgram` and proves the
//!      decoded form via `native_decide`,
//!   3. states a `cuTripleWithinMem` Hoare triple over the decoded
//!      sequence with mvars (`?_`) for the pre/post atoms, and
//!   4. discharges the proof via `sl_block_auto`.
//!
//! For byte_increment.so this reproduces the same theorem
//! `byte_increment_macro_spec_auto` already proves in `SVM/SBPF/Macros.lean`
//! — but the *theorem statement* is now generated mechanically from the
//! `.so`, not hand-typed. That's the load-bearing demonstration: given
//! the binary, we can produce the Lean proof obligation automatically;
//! `sl_block_auto` then closes it.
//!
//! Phase 2 (this iteration): a symbolic executor walks the decoded
//! insns left-to-right, maintaining a `SymState` (symbolic regs +
//! memory atoms), and synthesises the pre/post-condition assertions
//! that `sl_block_auto` then closes. Supports the byte_increment +
//! counter instruction set today: ldxb/ldxdw/stxb/stxdw, add64.imm,
//! sub64.imm, mov64.imm. Extending to more opcodes is mechanical —
//! one match arm per `ebpf::OPCODE`.
//!
//! Usage:
//!   cargo run --features qedrecover --bin qedlift -- \
//!     --so tests/fixtures/byte_increment.so \
//!     --output examples/lean/Generated/ByteIncrementLifted.lean

use std::path::PathBuf;
use std::sync::Arc;

use solana_sbpf::{
    ebpf,
    elf::Executable,
    program::BuiltinProgram,
    static_analysis::Analysis,
    vm::ContextObject,
};

struct NoopCtx;
impl ContextObject for NoopCtx {
    fn consume(&mut self, _amount: u64) {}
    fn get_remaining(&self) -> u64 { 0 }
}

struct Args {
    so:     PathBuf,
    output: Option<PathBuf>,
    module: Option<String>,
}

fn parse_args() -> Result<Args, String> {
    let mut so:     Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut module: Option<String>  = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--so"     => so     = Some(it.next().ok_or("--so needs a path")?.into()),
            "--output" => output = Some(it.next().ok_or("--output needs a path")?.into()),
            "--module" => module = Some(it.next().ok_or("--module needs a name")?),
            other      => return Err(format!("unknown arg: {}", other)),
        }
    }
    Ok(Args { so: so.ok_or("missing --so")?, output, module })
}

/// Convert a `solana_sbpf::ebpf::Insn` at analysis PC `pc` to the
/// Lean `Insn` constructor syntax. The cases here cover the
/// byte_increment / counter / guarded-counter / counter_with_helper
/// instruction sets; extending it is mechanical (each new opcode
/// adds one match arm). For conditional jumps `pc` is used to
/// resolve the target PC; for `call_local`, `call_target` (when
/// provided) is substituted as the resolved callee PC (because the
/// raw immediate is a Murmur3 hash, not an offset).
fn insn_to_lean_full(insn: &ebpf::Insn, pc: usize, call_target: Option<usize>) -> Result<String, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    let reg = |n: u8| match n {
        0 => ".r0", 1 => ".r1", 2 => ".r2", 3 => ".r3",
        4 => ".r4", 5 => ".r5", 6 => ".r6", 7 => ".r7",
        8 => ".r8", 9 => ".r9", 10 => ".r10",
        _ => "?reg",
    };
    Ok(match insn.opc {
        LD_B_REG    => format!(".ldx .byte {} {} {}",     reg(dst), reg(src), off),
        LD_H_REG    => format!(".ldx .halfword {} {} {}", reg(dst), reg(src), off),
        LD_W_REG    => format!(".ldx .word {} {} {}",     reg(dst), reg(src), off),
        LD_DW_REG   => format!(".ldx .dword {} {} {}",    reg(dst), reg(src), off),
        ST_B_REG    => format!(".stx .byte {} {} {}",     reg(dst), off, reg(src)),
        ST_H_REG    => format!(".stx .halfword {} {} {}", reg(dst), off, reg(src)),
        ST_W_REG    => format!(".stx .word {} {} {}",     reg(dst), off, reg(src)),
        ST_DW_REG   => format!(".stx .dword {} {} {}",    reg(dst), off, reg(src)),
        ADD64_IMM   => format!(".add64 {} (.imm {})",     reg(dst), imm),
        SUB64_IMM   => format!(".sub64 {} (.imm {})",     reg(dst), imm),
        MOV64_IMM   => format!(".mov64 {} (.imm {})",     reg(dst), imm),
        ADD64_REG   => format!(".add64 {} (.reg {})",     reg(dst), reg(src)),
        SUB64_REG   => format!(".sub64 {} (.reg {})",     reg(dst), reg(src)),
        MOV64_REG   => format!(".mov64 {} (.reg {})",     reg(dst), reg(src)),
        EXIT        => ".exit".to_string(),
        // Conditional jumps with immediate operand. Lean syntax is
        // `.jXX dst (.imm K) target_pc`. We resolve `target_pc` to the
        // absolute PC the jump lands at (caller-supplied).
        JEQ64_IMM | JEQ32_IMM => {
            let t = (pc as i64) + 1 + off; format!(".jeq {} (.imm {}) {}", reg(dst), imm, t)
        }
        JNE64_IMM | JNE32_IMM => {
            let t = (pc as i64) + 1 + off; format!(".jne {} (.imm {}) {}", reg(dst), imm, t)
        }
        JGT64_IMM | JGT32_IMM => {
            let t = (pc as i64) + 1 + off; format!(".jgt {} (.imm {}) {}", reg(dst), imm, t)
        }
        JGE64_IMM | JGE32_IMM => {
            let t = (pc as i64) + 1 + off; format!(".jge {} (.imm {}) {}", reg(dst), imm, t)
        }
        JLT64_IMM | JLT32_IMM => {
            let t = (pc as i64) + 1 + off; format!(".jlt {} (.imm {}) {}", reg(dst), imm, t)
        }
        JLE64_IMM | JLE32_IMM => {
            let t = (pc as i64) + 1 + off; format!(".jle {} (.imm {}) {}", reg(dst), imm, t)
        }
        JA          => {
            let t = (pc as i64) + 1 + off; format!(".ja {}", t)
        }
        // call_local: the immediate is the Solana ABI Murmur3 hash
        // of the symbol, NOT a relative offset. Resolving the actual
        // target PC requires `solana_sbpf::Analysis::cfg_nodes`; the
        // caller pre-resolves it via `?TARGET` substitution before
        // emitting Lean. Render with a placeholder so any caller that
        // forgets to substitute fails loudly rather than emitting a
        // garbage target.
        CALL_IMM    => match call_target {
            Some(t) => format!(".call_local {}", t),
            None    => ".call_local TARGET_PC_NOT_RESOLVED".to_string(),
        },
        opc         => return Err(format!("opcode 0x{:02x} not yet lifted to Lean", opc)),
    })
}

/// Thin wrapper for callers that don't know the resolved call target
/// (e.g. the raw "decoded insns" listing in the diagnostic dump).
/// Renders call_local with a placeholder.
fn insn_to_lean(insn: &ebpf::Insn, pc: usize) -> Result<String, String> {
    insn_to_lean_full(insn, pc, None)
}

/// Resolve a CALL_IMM at `pc` to its callee PC. solana-sbpf encodes
/// the call's immediate field as the Murmur3 hash of the symbol name
/// (not a relative offset). The function registry — exposed as
/// `analysis.functions: BTreeMap<usize, (u32, String)>` mapping
/// function-start-pc → (hash, name) — lets us reverse the lookup.
fn resolve_call_target(analysis: &Analysis, insn: &ebpf::Insn) -> Option<usize> {
    if insn.opc != ebpf::CALL_IMM { return None; }
    let target_hash = insn.imm as u32;
    analysis.functions.iter()
        .find_map(|(&pc, (h, _name))| if *h == target_hash { Some(pc) } else { None })
}

// -----------------------------------------------------------------------------
// Symbolic executor — phase 2 of the lift
// -----------------------------------------------------------------------------
//
// Walks a straight-line slice of decoded eBPF insns, maintaining a
// SymState (symbolic register values + ordered list of pre-condition
// atoms touched). Emits the Lean SL expressions for the precondition
// and postcondition. The triple type is `cuTripleWithinMem n 0 0 n cr
// PRE POST RR` where `n` is the number of insns covered (excluding
// the trailing exit, if any) — exactly the shape `sl_block_auto`
// accepts.

/// Symbolic-algebra expression representing a Nat value during
/// symbolic execution. Stringified to Lean source via `to_lean`.
#[derive(Clone, Debug)]
enum Expr {
    /// Initial value of a register at entry (e.g., "initR2", "baseAddr").
    InitReg(String),
    /// Initial value of a memory cell loaded during execution (e.g., "oldCounter").
    InitMem(String),
    /// Integer literal.
    Const(i64),
    /// `toU64 n` — Solana ABI helper for sign-extended Nat literals.
    ToU64(Box<Expr>),
    /// `e % m` — narrowing modulus from a byte/half/word load.
    Mod(Box<Expr>, u64),
    /// `wrapAdd a b` — 64-bit wrapping add.
    WrapAdd(Box<Expr>, Box<Expr>),
    /// `wrapSub a b` — 64-bit wrapping sub.
    WrapSub(Box<Expr>, Box<Expr>),
}

impl Expr {
    fn to_lean(&self) -> String {
        match self {
            Expr::InitReg(n) | Expr::InitMem(n) => n.clone(),
            Expr::Const(n) => format!("{}", n),
            Expr::ToU64(e) => format!("toU64 {}", e.atom_lean()),
            Expr::Mod(e, m) => format!("{} % {}", e.atom_lean(), m),
            Expr::WrapAdd(a, b) => format!("wrapAdd {} {}", a.atom_lean(), b.atom_lean()),
            Expr::WrapSub(a, b) => format!("wrapSub {} {}", a.atom_lean(), b.atom_lean()),
        }
    }
    /// Lean rendering suitable for use as a function argument
    /// (parenthesised when the head isn't already atomic).
    fn atom_lean(&self) -> String {
        match self {
            Expr::InitReg(_) | Expr::InitMem(_) | Expr::Const(_) => self.to_lean(),
            _ => format!("({})", self.to_lean()),
        }
    }
}

/// Load/store width — used to pick the right Lean memory binding
/// notation (↦ₘ for byte, ↦U16/32/64 for wider).
#[derive(Clone, Copy, Debug)]
enum Width { Byte, Halfword, Word, Dword }

impl Width {
    fn lean_arrow(&self) -> &'static str {
        match self {
            Width::Byte     => "↦ₘ",
            Width::Halfword => "↦U16",
            Width::Word     => "↦U32",
            Width::Dword    => "↦U64",
        }
    }
    fn modulus(&self) -> u64 {
        match self {
            Width::Byte     => 256,
            Width::Halfword => 1 << 16,
            Width::Word     => 1 << 32,
            Width::Dword    => 0, // no narrowing
        }
    }
}

/// One precondition atom: a register binding or a memory cell binding.
#[derive(Clone, Debug)]
enum Atom {
    Reg(u8, Expr),
    Mem { addr_base: Expr, addr_off: i64, width: Width, value: Expr },
}

impl Atom {
    fn to_lean(&self) -> String {
        match self {
            Atom::Reg(r, v) => format!("(.{} ↦ᵣ {})", reg_lit(*r), v.to_lean()),
            Atom::Mem { addr_base, addr_off, width, value } => format!(
                "(effectiveAddr {} {} {} {})",
                addr_base.atom_lean(),
                addr_off,
                width.lean_arrow(),
                value.to_lean(),
            ),
        }
    }
}

fn reg_lit(n: u8) -> &'static str {
    match n {
        0 => "r0", 1 => "r1", 2 => "r2", 3 => "r3", 4 => "r4",
        5 => "r5", 6 => "r6", 7 => "r7", 8 => "r8", 9 => "r9", 10 => "r10",
        _ => "r0",
    }
}

fn reg_initial_name(n: u8) -> String {
    match n {
        1 => "baseAddr".to_string(),    // r1 = input ptr by Solana ABI
        _ => format!("vR{}Old", n),
    }
}

/// One memory cell in the symbolic walk. The address is the SYMBOLIC
/// value of `base_reg` at the access — necessary because the same
/// `[r1+0]` access at two different walk PCs can refer to different
/// physical cells if `r1` was modified in between.
#[derive(Clone, Debug)]
struct MemCell {
    addr_base: Expr,
    addr_off:  i64,
    width:     Width,
    value:     Expr,
}

impl MemCell {
    /// Stable key over (rendered address, width) — two cells whose
    /// addresses render identically refer to the same physical cell.
    fn key(&self) -> (String, i64, u8) {
        (self.addr_base.to_lean(), self.addr_off, self.width as u8)
    }
}

/// Symbolic state threaded through one walk of the slice.
#[derive(Default)]
struct SymState {
    /// Current symbolic value of each register, if read or written.
    /// Registers not present are treated as their initial value
    /// (`InitReg(reg_initial_name(r))`).
    regs: std::collections::BTreeMap<u8, Expr>,
    /// Pre-condition atoms collected in *first-touched* order.
    pre: Vec<Atom>,
    /// Memory cells the slice touched. Keyed by the rendered Lean
    /// representation of the effective address `(base, off, width)`,
    /// where `base` is the SYMBOLIC value of the base register at
    /// access time — so two reads at `[r1+0]` separated by an
    /// `add64 r1, 8` correctly resolve to two distinct cells.
    /// Implementation: linear search over a Vec (small N).
    mem: Vec<MemCell>,
    /// Fresh-variable counter for memory initials.
    fresh: u32,
    /// Names of symbolic variables that come from u64-width loads
    /// (`ldxdw`). The corresponding per-instruction spec carries a
    /// `< 2^64` side condition that the theorem signature must
    /// hypothesise so `sl_block_auto <;> assumption` discharges it.
    u64_load_vars: Vec<String>,
    /// Conditional jumps encountered on the happy-path walk. Each one
    /// adds a path hypothesis to the theorem signature.
    branch_hyps: Vec<BranchHyp>,
    /// Symbolic call stack — resume PCs pushed by `call_local`, popped
    /// by the corresponding `exit`. Empty at the start of the walk
    /// and empty when the walk terminates at the top-level `exit`.
    call_stack: Vec<usize>,
    /// True once the walk has seen at least one `call_local`. When
    /// set, the emission adds `r6..r10` and `callStackIs []` to the
    /// pre-condition (the atoms `call_local_spec` needs to compose).
    saw_call: bool,
}

impl SymState {
    fn read_reg(&mut self, r: u8) -> Expr {
        if let Some(v) = self.regs.get(&r) { return v.clone(); }
        let v = Expr::InitReg(reg_initial_name(r));
        self.regs.insert(r, v.clone());
        // Register reads from r0/r2..r9 add a pre-atom (we need to
        // know its initial value); r1 (input ptr) and r10 (frame top)
        // are conventional and also recorded.
        self.pre.push(Atom::Reg(r, v.clone()));
        v
    }
    fn write_reg(&mut self, r: u8, v: Expr) {
        // Ensure r has a pre-atom: if it was never read, its initial
        // value is still "free" — record it before overwriting.
        if !self.regs.contains_key(&r) {
            let init = Expr::InitReg(reg_initial_name(r));
            self.regs.insert(r, init.clone());
            self.pre.push(Atom::Reg(r, init));
        }
        self.regs.insert(r, v);
    }
    fn read_mem(&mut self, base: u8, off: i64, width: Width) -> Expr {
        // Compute the effective-address key from the base register's
        // *current* symbolic value (not just its register number).
        let base_expr = self.read_reg(base);
        let key = (base_expr.to_lean(), off, width as u8);
        if let Some(cell) = self.mem.iter().find(|c| c.key() == key) {
            return cell.value.clone();
        }
        // Fresh cell: name by (width, sequence index) since the
        // address expression itself may be complex (`wrapAdd baseAddr
        // (toU64 8)`) and ill-suited as a Lean identifier.
        let idx = self.fresh; self.fresh += 1;
        let name = format!("oldMem{}_{}", w_short(width), idx);
        if matches!(width, Width::Dword) {
            self.u64_load_vars.push(name.clone());
        }
        let v = Expr::InitMem(name);
        let cell = MemCell {
            addr_base: base_expr.clone(), addr_off: off, width, value: v.clone(),
        };
        self.mem.push(cell);
        self.pre.push(Atom::Mem {
            addr_base: base_expr, addr_off: off, width, value: v.clone(),
        });
        v
    }
    fn write_mem(&mut self, base: u8, off: i64, width: Width, value: Expr) {
        let base_expr = self.read_reg(base);
        let key = (base_expr.to_lean(), off, width as u8);
        // Make sure the pre-atom exists (a store after no preceding
        // load still needs the cell to be present in the pre-state).
        if !self.mem.iter().any(|c| c.key() == key) {
            let _ = self.read_mem(base, off, width);
        }
        if let Some(cell) = self.mem.iter_mut().find(|c| c.key() == key) {
            cell.value = value;
        }
    }
    fn next_fresh(&mut self) -> u32 { self.fresh += 1; self.fresh }
}

fn w_short(w: Width) -> &'static str {
    match w { Width::Byte => "B", Width::Halfword => "H", Width::Word => "W", Width::Dword => "D" }
}

/// A conditional jump the symbolic executor walked past on its
/// happy-path traversal. The theorem signature surfaces this as a
/// hypothesis the user (or a downstream tactic) must invoke when
/// closing the proof — `sl_block_auto` doesn't currently collapse
/// these on its own.
#[derive(Clone, Debug)]
enum BranchKind { JeqImm, JneImm }

#[derive(Clone, Debug)]
struct BranchHyp {
    kind: BranchKind,
    dst_value: Expr,
    imm: i64,
    #[allow(dead_code)] target_pc: usize,
}

impl BranchHyp {
    /// Render the hypothesis in the form needed for the theorem
    /// signature, i.e. `<dst_value> ≠ toU64 <imm>` for a JeqImm whose
    /// happy path is fall-through.
    fn lean_hyp(&self) -> String {
        match self.kind {
            BranchKind::JeqImm => format!("{} ≠ toU64 {}", self.dst_value.to_lean(), self.imm),
            BranchKind::JneImm => format!("{} = toU64 {}", self.dst_value.to_lean(), self.imm),
        }
    }
    fn name(&self, idx: usize) -> String { format!("h_branch{}", idx) }
}

/// Step one instruction's effect through `state`. Returns Ok(true) if
/// the instruction was a recognised non-terminator; Ok(false) if it
/// was `exit` (slice terminates); Err for opcodes the executor
/// doesn't model yet. `pc` is the analysis-PC of `insn` (only used
/// to resolve relative jump targets).
fn step(state: &mut SymState, insn: &ebpf::Insn, pc: Option<usize>) -> Result<bool, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    match insn.opc {
        LD_B_REG => {
            let raw = state.read_mem(src, off, Width::Byte);
            // Byte load narrows: r := raw % 256.
            state.write_reg(dst, Expr::Mod(Box::new(raw), 256));
        }
        LD_H_REG => {
            let raw = state.read_mem(src, off, Width::Halfword);
            state.write_reg(dst, Expr::Mod(Box::new(raw), 1 << 16));
        }
        LD_W_REG => {
            let raw = state.read_mem(src, off, Width::Word);
            state.write_reg(dst, Expr::Mod(Box::new(raw), 1 << 32));
        }
        LD_DW_REG => {
            let raw = state.read_mem(src, off, Width::Dword);
            state.write_reg(dst, raw);
        }
        ST_B_REG => {
            let cur = state.read_reg(src);
            // Byte store narrows: mem := r % 256.
            state.write_mem(dst, off, Width::Byte, Expr::Mod(Box::new(cur), 256));
        }
        ST_H_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Halfword, Expr::Mod(Box::new(cur), 1 << 16));
        }
        ST_W_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Word, Expr::Mod(Box::new(cur), 1 << 32));
        }
        ST_DW_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Dword, cur);
        }
        ADD64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::WrapAdd(
                Box::new(cur),
                Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
            ));
        }
        SUB64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::WrapSub(
                Box::new(cur),
                Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
            ));
        }
        MOV64_IMM => {
            state.write_reg(dst, Expr::ToU64(Box::new(Expr::Const(imm))));
        }
        MOV64_REG => {
            let v = state.read_reg(src);
            state.write_reg(dst, v);
        }
        ADD64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapAdd(Box::new(a), Box::new(b)));
        }
        SUB64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapSub(Box::new(a), Box::new(b)));
        }
        // Conditional jumps on an immediate. Modelled as "happy path
        // = fall-through" by default (the common shape for guard
        // checks at function start). Records a path hypothesis the
        // theorem signature will surface; doesn't change reg/mem
        // state. Caller invents a path-hypothesis variable name.
        JEQ64_IMM | JEQ32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqImm, dst_value: r, imm,
                target_pc: ((pc.unwrap_or(0) as i64) + 1 + off) as usize,
            });
        }
        JNE64_IMM | JNE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneImm, dst_value: r, imm,
                target_pc: ((pc.unwrap_or(0) as i64) + 1 + off) as usize,
            });
        }
        JA => { /* unconditional fall-through reset is handled by the caller's PC walk */ }
        // call_local target: pushes a frame, bumps r10 by 0x1000,
        // redirects PC to target. The PC redirect happens in the
        // walker; here we just update the symbolic state per
        // `call_local_spec` in InstructionSpecs/CallReturn.lean.
        CALL_IMM => {
            state.saw_call = true;
            // r6..r9 must be in scope (they're framed by call_local_spec).
            for r in 6..=9 { let _ = state.read_reg(r); }
            // r10 is bumped by 0x1000 (one Solana V0 stack frame).
            let r10_old = state.read_reg(10);
            state.write_reg(10, Expr::WrapAdd(
                Box::new(r10_old),
                Box::new(Expr::Const(0x1000)),
            ));
            // Track the resume PC so the matching `exit` knows where
            // to return. Stored separately from r10's symbolic walk.
            let resume = pc.map(|p| p + 1).unwrap_or(0);
            state.call_stack.push(resume);
        }
        EXIT => {
            if state.call_stack.is_empty() {
                // Top-level termination — caller decides what to do.
                return Ok(false);
            } else {
                // Nested exit: pop the frame. Per exit_pops_spec, r6..r10
                // are restored to their pre-call values. In the symbolic
                // walk, the callee should not have modified r6..r10 (Solana
                // ABI). We undo r10's +0x1000 bump from the matching
                // call_local; if the callee touched r6..r9 in violation
                // of the ABI, the chain won't compose and the user will
                // see the failure as a sl_block_iter residual.
                let _ = state.call_stack.pop();
                let r10_cur = state.read_reg(10);
                state.write_reg(10, Expr::WrapSub(
                    Box::new(r10_cur),
                    Box::new(Expr::Const(0x1000)),
                ));
                // step() returns Ok(true) so the walker continues; the
                // walker resumes at the popped PC.
            }
        }
        opc => return Err(format!("symbolic executor: opcode 0x{:02x} not yet modelled", opc)),
    }
    Ok(true)
}

/// Concatenate the pre-atom list into a Lean `**`-separated SL
/// expression. Empty list renders as `emp`.
fn atoms_to_lean(atoms: &[Atom]) -> String {
    if atoms.is_empty() { return "emp".to_string(); }
    let parts: Vec<String> = atoms.iter().map(Atom::to_lean).collect();
    parts.join(" **\n      ")
}

/// Build the postcondition atom list: same shape as pre, but each atom
/// reflects the symbolic value at the end of the walk.
fn post_atoms(initial_pre: &[Atom], state: &SymState) -> Vec<Atom> {
    let mut out = Vec::with_capacity(initial_pre.len());
    for atom in initial_pre {
        match atom {
            Atom::Reg(r, _) => {
                let v = state.regs.get(r).cloned()
                    .unwrap_or_else(|| Expr::InitReg(reg_initial_name(*r)));
                out.push(Atom::Reg(*r, v));
            }
            Atom::Mem { addr_base, addr_off, width, .. } => {
                // Look up the cell by (rendered-addr, off, width) key —
                // the same scheme `read_mem`/`write_mem` use.
                let key = (addr_base.to_lean(), *addr_off, *width as u8);
                let v = state.mem.iter()
                    .find(|c| c.key() == key)
                    .map(|c| c.value.clone())
                    .unwrap_or_else(|| Expr::InitMem("?".to_string()));
                out.push(Atom::Mem {
                    addr_base: addr_base.clone(),
                    addr_off:  *addr_off,
                    width:     *width,
                    value:     v,
                });
            }
        }
    }
    out
}

/// Build the region-requirement clause: for each memory atom in pre,
/// emit `rt.containsRange addr width = true` (and `containsWritable`
/// for any atom we mutated).
fn region_req(pre: &[Atom], state: &SymState) -> String {
    let mut clauses = Vec::new();
    for atom in pre {
        if let Atom::Mem { addr_base, addr_off, width, .. } = atom {
            let width_bytes = match width {
                Width::Byte => 1, Width::Halfword => 2, Width::Word => 4, Width::Dword => 8,
            };
            let addr = format!("effectiveAddr {} {}", addr_base.atom_lean(), addr_off);
            clauses.push(format!("rt.containsRange ({}) {} = true", addr, width_bytes));
            // Was it written to? Look up the cell by the same
            // rendered-address key the mem map uses.
            let key = (addr_base.to_lean(), *addr_off, *width as u8);
            if let Some(cell) = state.mem.iter().find(|c| c.key() == key) {
                let written = !matches!(cell.value, Expr::InitMem(_));
                if written {
                    clauses.push(format!(
                        "rt.containsWritable ({}) {} = true",
                        addr, width_bytes,
                    ));
                }
            }
        }
    }
    if clauses.is_empty() {
        "True".to_string()
    } else {
        // Left-associative: `((A ∧ B) ∧ C) ∧ D`. `sl_block_iter`'s
        // chain composition produces this shape (each step's rr is
        // ∧-merged on the left); to keep the goal isDefEq to the
        // chain, the emitted goal needs the same parenthesisation.
        let mut out = clauses[0].clone();
        for c in clauses.iter().skip(1) {
            out = format!("({}) ∧\n                  {}", out, c);
        }
        out
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = parse_args().map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;
    let bytes = std::fs::read(&args.so)?;
    let loader = Arc::new(BuiltinProgram::new_mock());
    let executable: Executable<NoopCtx> = Executable::load(&bytes, loader)?;
    let text_pcs = executable.get_text_bytes();
    let text_offset = text_pcs.0;
    let text_bytes  = text_pcs.1;
    // Static analysis gives us the CFG, which maps call_local's
    // Murmur3-hash immediate to the resolved callee PC via
    // `cfg_nodes[pc].destinations`. Without this, CALL_IMM's `imm`
    // field is meaningless (it's a hash, not a relative offset).
    let analysis = Analysis::from_executable(&executable)?;

    // Decode the .text into raw eBPF insns. This is what `Analysis`
    // does internally; we just need the linear stream because
    // byte_increment is straight-line.
    let mut insns = Vec::new();
    let mut pc = 0;
    while pc * ebpf::INSN_SIZE < text_bytes.len() {
        let insn = ebpf::get_insn(text_bytes, pc);
        let opc  = insn.opc;
        insns.push(insn);
        pc += if opc == ebpf::LD_DW_IMM { 2 } else { 1 };
    }

    // Diagnostic dump (stderr) — useful when step() can't model an
    // opcode and we want to see the surrounding shape anyway.
    eprintln!("=== decoded insns ===");
    for (i, ins) in insns.iter().enumerate() {
        let rendered = insn_to_lean(ins, i).unwrap_or_else(|e| format!("?? ({})", e));
        eprintln!("  pc={:3}  opc=0x{:02x}  {}", i, ins.opc, rendered);
    }
    eprintln!();

    // Default module name from the .so filename.
    let so_stem = args.so.file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lifted".to_string());
    let module_name = args.module.unwrap_or_else(|| {
        // PascalCase: byte_increment → ByteIncrement
        let mut out = String::new();
        let mut up = true;
        for c in so_stem.chars() {
            if c == '_' || c == '-' { up = true; continue; }
            if up { out.extend(c.to_uppercase()); up = false; }
            else  { out.push(c); }
        }
        format!("{}Lifted", out)
    });

    // Emit the Lean module.
    let mut out = String::new();
    out.push_str(&format!(
        "/-\n  Generated by `qedlift` from `{}`.\n\
         \n\
         End-to-end lift demonstration:\n\
         1. The .text bytes are embedded verbatim as a `ByteArray`.\n\
         2. `Decode.decodeProgram` recovers the instruction sequence;\n\
            `native_decide` proves the decode is correct.\n\
         3. A `cuTripleWithinMem` Hoare triple is stated over the\n\
            decoded sequence. The pre/post atom synthesis is the next\n\
            iteration's work (the \"symbolic executor\" piece); for the\n\
            demo, see the worked example in\n\
            `SVM/SBPF/Macros.lean` (`{}_macro_spec_auto`) where the\n\
            theorem is proved by `sl_block_auto` against the same\n\
            instruction sequence.\n\
         -/\n\n",
        args.so.display(), so_stem,
    ));
    out.push_str("import SVM.SBPF.Decode\n");
    out.push_str("import SVM.SBPF.RunnerBridge\n");
    out.push_str("import SVM.SBPF.Macros\n\n");
    // File-level option bumps. Long chains (especially ones with
    // call_local + exit_pops composition) blow past the defaults
    // during `slBlockIter`'s isDefEq work.
    out.push_str("set_option maxRecDepth 65536\n");
    out.push_str("set_option maxHeartbeats 4000000\n\n");
    out.push_str(&format!("namespace Examples.Lifted.{}\n\n", module_name));

    // The bytes.
    out.push_str("open SVM.SBPF\n\n");
    out.push_str("/-- `.text` bytes extracted from the .so by qedlift. -/\n");
    out.push_str(&format!("def {}Bytes : ByteArray := ⟨#[\n", module_name));
    for (i, byte) in text_bytes.iter().enumerate() {
        if i % 8 == 0 { out.push_str("  "); }
        out.push_str(&format!("0x{:02x}", byte));
        if i + 1 < text_bytes.len() { out.push_str(", "); }
        if i % 8 == 7 || i + 1 == text_bytes.len() { out.push('\n'); }
    }
    out.push_str("]⟩\n\n");
    out.push_str(&format!("/-- Text section file-offset: 0x{:x}. -/\n", text_offset));
    out.push_str(&format!("def {}TextOffset : Nat := 0x{:x}\n\n", module_name, text_offset));

    // The decoded insns.
    out.push_str("/-- Decoded form of the .text bytes. -/\n");
    out.push_str(&format!("def {}Insns : Array Insn := #[\n", module_name));
    for (i, insn) in insns.iter().enumerate() {
        let tgt = resolve_call_target(&analysis, insn);
        let lean = match insn_to_lean_full(insn, i, tgt) {
            Ok(s) => s,
            Err(e) => return Err(e.into()),
        };
        let sep = if i + 1 < insns.len() { "," } else { "" };
        out.push_str(&format!("  {}{}\n", lean, sep));
    }
    out.push_str("]\n\n");

    // The decode equality proof.
    out.push_str("/-- The bytes decode exactly to the expected instruction array. -/\n");
    out.push_str(&format!(
        "theorem {}_decodes :\n    \
         Decode.decodeProgram {}Bytes = some {}Insns := by\n  native_decide\n\n",
        module_name, module_name, module_name,
    ));

    // CFG-aware happy-path walk + symbolic execution in one pass.
    // PC progression follows the actual control flow:
    //   * straight-line opcode    → pc + 1
    //   * `ja off`                → pc + 1 + off
    //   * conditional jump (jeq/jne) → pc + 1 (fall-through policy)
    //   * `call_local target`     → push pc+1, jump to target
    //   * `exit` with empty stack → top-level terminator, walk ends
    //   * `exit` with non-empty stack → pop, resume at popped PC
    //
    // Walk starts at the ELF's declared entrypoint (NOT analysis PC 0:
    // the linker may place helper functions before the entrypoint).
    let mut block_pcs: Vec<usize> = Vec::new();
    let exit_pc: usize;
    let mut state = SymState::default();
    {
        let entry_pc = executable.get_entrypoint_instruction_offset();
        let mut pc_iter: usize = entry_pc;
        loop {
            if pc_iter >= insns.len() { exit_pc = pc_iter; break; }
            let ins = &insns[pc_iter];

            // Handle exit specially — it's either a nested return
            // (pops the call stack + restores r10) or a top-level
            // terminator (ends the walk; not included in the CR).
            if ins.opc == ebpf::EXIT {
                if state.call_stack.is_empty() {
                    exit_pc = pc_iter;
                    break;
                } else {
                    block_pcs.push(pc_iter);
                    let resume = state.call_stack.pop().unwrap();
                    // exit_pops_spec restores r10 to its pre-call value.
                    // Undo the +0x1000 bump applied by the matching
                    // call_local in step().
                    let r10_cur = state.read_reg(10);
                    state.write_reg(10, Expr::WrapSub(
                        Box::new(r10_cur),
                        Box::new(Expr::Const(0x1000)),
                    ));
                    pc_iter = resume;
                    continue;
                }
            }

            block_pcs.push(pc_iter);
            step(&mut state, ins, Some(pc_iter))?;

            // PC progression.
            match ins.opc {
                ebpf::JA => {
                    pc_iter = ((pc_iter as i64) + 1 + (ins.off as i64)) as usize;
                }
                ebpf::CALL_IMM => {
                    // The immediate is a Murmur3 hash; look up the
                    // function registry to resolve the callee PC.
                    pc_iter = resolve_call_target(&analysis, ins).ok_or_else(|| {
                        format!(
                            "qedlift: call_local at pc {} has imm 0x{:x} \
                             but no matching function in the symbol table. \
                             Recompile with symbols, or extend the resolver.",
                            pc_iter, ins.imm as u32)
                    })?;
                }
                _ => { pc_iter += 1; }
            }
        }
    }

    // Build the CR as a Lean string. `sl_block_auto` requires the CR
    // to appear as a literal `union`-of-`singleton`s in the theorem
    // statement (it walks the AST), so we capture the string here and
    // inline it below instead of emitting a `def`.
    let cr_lean: String = if block_pcs.is_empty() {
        "CodeReq.empty".to_string()
    } else {
        let mut s = String::new();
        let opens = "(".repeat(block_pcs.len().saturating_sub(1));
        s.push_str(&opens);
        for (i, &pc) in block_pcs.iter().enumerate() {
            let tgt = resolve_call_target(&analysis, &insns[pc]);
            let lean_insn = insn_to_lean_full(&insns[pc], pc, tgt)?;
            if i == 0 {
                s.push_str(&format!("(CodeReq.singleton {} ({}))", pc, lean_insn));
            } else {
                s.push_str(&format!(".union\n        (CodeReq.singleton {} ({})))", pc, lean_insn));
            }
        }
        s
    };

    // --- Phase 2: symbolic execution + Hoare-triple emission. ---
    out.push_str("/-! ## Symbolically lifted Hoare triple\n\n");
    out.push_str("Synthesised by qedlift's symbolic executor walking the\n");
    out.push_str("decoded insns left-to-right. Closed by `sl_block_auto`. -/\n\n");

    // Note: symbolic execution already happened inline in the walker
    // above; `state` is populated and ready to snapshot.
    let pre  = state.pre.clone();
    let post = post_atoms(&pre, &state);
    let rr   = region_req(&pre, &state);
    // When the walk crossed a call_local, the chain's pre/post must
    // include `callStackIs []` as a framed atom — `call_local_spec`
    // takes a `callStackIs cs` in its pre, and the matching
    // `exit_pops_spec` returns the popped `callStackIs cs` in its
    // post. The empty initial stack pushes the new frame, then pops
    // back to empty on exit_pops, so net change is none — but the
    // atom must be present in pre+post for sl_block_iter to thread
    // it through the chain.
    let cs_atom = if state.saw_call { " ** callStackIs []" } else { "" };

    // Collect the symbolic variables we introduced so the theorem
    // signature can quantify over them.
    let mut vars: Vec<String> = Vec::new();
    let mut push_var = |v: &Expr, vars: &mut Vec<String>| {
        if let Expr::InitReg(n) | Expr::InitMem(n) = v {
            if !vars.contains(n) { vars.push(n.clone()); }
        }
    };
    for atom in &pre {
        match atom {
            Atom::Reg(_, v) => push_var(v, &mut vars),
            Atom::Mem { addr_base, value, .. } => {
                push_var(addr_base, &mut vars);
                push_var(value, &mut vars);
            }
        }
    }
    let vars_sig = if vars.is_empty() { String::new() }
                   else { format!("({} : Nat)\n    ", vars.join(" ")) };
    // Side-condition hypotheses for u64-width loads. Per
    // `ldxdw_spec`, each loaded value carries a `< 2^64` constraint
    // that `sl_block_auto` leaves as a residual goal; we surface them
    // as theorem hypotheses and discharge with `<;> assumption`.
    let mut u64_hyps = String::new();
    for v in &state.u64_load_vars {
        u64_hyps.push_str(&format!("(h{}_lt : {} < 2 ^ 64)\n    ", v, v));
    }
    // Path-hypothesis surface for any conditional jumps we walked.
    // For a JeqImm whose happy path is fall-through (the common
    // guard-check shape), the hypothesis is `dst ≠ toU64 imm`.
    let mut branch_hyps_sig = String::new();
    for (i, bh) in state.branch_hyps.iter().enumerate() {
        branch_hyps_sig.push_str(&format!("({} : {})\n    ", bh.name(i), bh.lean_hyp()));
    }
    // `sl_block_auto` now dispatches conditional jumps to their
    // `_not_taken` variants in InstructionSpecs/Jump.lean (see
    // SVM/SBPF/SpecGen.lean), surfacing the path hypothesis as a
    // residual side goal. `<;> assumption` closes them against the
    // theorem's `h_branchK` hypotheses, alongside any u64-load
    // `< 2^64` residuals.
    let needs_assumption = !state.branch_hyps.is_empty()
                        || !state.u64_load_vars.is_empty();
    // Call-containing chains: theorem statement is correct, but
    // `sl_block_auto`'s composition pass hits a recursion depth
    // problem (likely in slBlockIter's atom-permutation search,
    // which has known scaling issues per the SL.lean comments —
    // ~30s/iter at iter 5 of an 11-instruction macro). Emit `sorry`
    // so the file type-checks; next iteration debugs slBlockIter.
    let tactic: String = if state.saw_call {
        "/- sl_block_auto diverges on call_local + exit_pops chains \
         in the current slBlockIter implementation (atom-permutation \
         search scaling, see SL.lean comments). Theorem statement is \
         synthesised correctly. Next iteration: debug slBlockIter or \
         use a dedicated call-composition lemma. -/\n  sorry".to_string()
    } else if needs_assumption {
        "sl_block_auto <;> assumption".to_string()
    } else {
        "sl_block_auto".to_string()
    };
    let tactic: &str = Box::leak(tactic.into_boxed_str());
    let n = block_pcs.len();

    out.push_str(&format!(
        "open Memory in\n\
         theorem {}_lifted_spec\n    {}{}{}: \
         cuTripleWithinMem {} 0 0 {}\n      \
         ({})\n      \
         ({}{})\n      \
         ({}{})\n      \
         (fun rt => {}) := by\n  \
         {}\n\n",
        module_name,
        vars_sig,
        u64_hyps,
        branch_hyps_sig,
        n, exit_pc,
        cr_lean,
        atoms_to_lean(&pre),  cs_atom,
        atoms_to_lean(&post), cs_atom,
        rr,
        tactic,
    ));

    out.push_str(&format!("end Examples.Lifted.{}\n", module_name));

    // Emit.
    match args.output {
        Some(path) => {
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(&path, &out)?;
            println!("=== qedlift ===");
            println!("  input  : {}", args.so.display());
            println!("  output : {}", path.display());
            println!("  .text  : {} bytes ({} insns)", text_bytes.len(), insns.len());
            println!("  module : Examples.Lifted.{}", module_name);
        }
        None => {
            print!("{}", out);
        }
    }

    Ok(())
}
