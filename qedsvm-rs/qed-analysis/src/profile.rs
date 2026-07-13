//! Trace profiling: turn a flat logical-PC execution trace into a
//! symbolicated listing and folded call stacks (flamegraph input).
//!
//! Input is a `.pcs`-style trace: logical PCs in execution order (what the
//! Lean runner's `TRACE_STEPS` emits, what qedlift's `--trace` consumes).
//! Pure analysis, Rust-side; the interpreter itself stays in Lean.
//!
//! # Weighting: steps, not CU
//!
//! [`fold_trace`] weights each frame by INSTRUCTION STEPS. Most sBPF
//! instructions cost 1 CU, so steps approximate CU, but syscalls cost more
//! (a `sol_sha256` is far from 1 CU), so a syscall-heavy frame is
//! under-weighted here. CU-exact weighting needs the per-syscall cost table
//! and is a follow-on. The output is honest as an instruction-hotspot
//! flamegraph.

use std::collections::BTreeMap;

use solana_sbpf::ebpf;

use crate::symbolicate::SymbolIndex;
use crate::PcMap;

/// One symbolicated step of an execution trace.
pub struct TraceStep {
    /// Logical PC (decoded-array index; same space as the `.pcs` trace).
    pub logical_pc: usize,
    /// Containing function, from the ELF symbol table.
    pub function: String,
    /// Inline frame chain at this PC (outermost first), empty without DWARF.
    pub inline: Vec<String>,
}

/// Symbolicate every step of `trace` (logical PCs) against `syms` + `map`.
pub fn symbolicate_trace(trace: &[usize], syms: &SymbolIndex, map: &PcMap) -> Vec<TraceStep> {
    trace
        .iter()
        .map(|&pc| TraceStep {
            logical_pc: pc,
            function: syms.label_logical(pc, map),
            inline: syms.inline_frames_logical(pc, map).unwrap_or_default(),
        })
        .collect()
}

/// Reconstruct the call stack across `trace` and fold it into `(stack, steps)`
/// pairs, most-visited first. `stack` is `caller;callee;...` (outermost first),
/// ready for `folded_lines`. `label(pc)` names the function containing a
/// logical PC; `insns` (indexed by logical PC) classifies call vs exit.
///
/// Frame model: a local `call` pushes the callee (identified by the next
/// traced PC, so no call-target resolution is needed); an `exit` pops. A
/// syscall `call` returns to `pc + 1` and does not push, so it is filtered by
/// comparing the next traced PC. See the module note on step-vs-CU weighting.
pub fn fold_trace(
    trace: &[usize],
    insns: &[ebpf::Insn],
    mut label: impl FnMut(usize) -> String,
) -> Vec<(String, u64)> {
    if trace.is_empty() {
        return Vec::new();
    }
    let mut folded: BTreeMap<String, u64> = BTreeMap::new();
    let mut stack: Vec<String> = vec![label(trace[0])];
    for (i, &pc) in trace.iter().enumerate() {
        *folded.entry(stack.join(";")).or_insert(0) += 1;
        match insns.get(pc).map(|n| n.opc) {
            Some(ebpf::EXIT) => {
                // Keep the root frame; a top-level exit ends the program.
                if stack.len() > 1 {
                    stack.pop();
                }
            }
            Some(op) if op == ebpf::CALL_IMM || op == ebpf::CALL_REG => {
                // Distinguish a local call (jumps to the callee entry) from a
                // syscall (returns to pc + 1) by the next traced PC.
                if let Some(&next) = trace.get(i + 1) {
                    if next != pc + 1 {
                        stack.push(label(next));
                    }
                }
            }
            _ => {}
        }
    }
    let mut out: Vec<(String, u64)> = folded.into_iter().collect();
    out.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    out
}

/// Render folded stacks as flamegraph.pl / inferno input: `stack count` lines.
pub fn folded_lines(folded: &[(String, u64)]) -> Vec<String> {
    folded.iter().map(|(s, c)| format!("{s} {c}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn insn(opc: u8) -> ebpf::Insn {
        ebpf::Insn {
            ptr: 0,
            opc,
            dst: 0,
            src: 0,
            off: 0,
            imm: 0,
        }
    }

    // Two functions: "main" occupies logical PCs 0..10, "helper" 10.. .
    fn label_two(pc: usize) -> String {
        if pc < 10 { "main" } else { "helper" }.to_string()
    }

    #[test]
    fn fold_reconstructs_call_and_return() {
        // main: pc0, pc1, call@pc2 -> helper: pc10, exit@pc11 -> main: pc3, exit@pc4.
        let mut insns = vec![insn(ebpf::MOV64_IMM); 12];
        insns[2] = insn(ebpf::CALL_IMM);
        insns[11] = insn(ebpf::EXIT);
        insns[4] = insn(ebpf::EXIT);
        let trace = [0usize, 1, 2, 10, 11, 3, 4];

        let folded = fold_trace(&trace, &insns, label_two);
        let map: BTreeMap<_, _> = folded.into_iter().collect();
        assert_eq!(map.get("main"), Some(&5)); // pc 0,1,2,3,4
        assert_eq!(map.get("main;helper"), Some(&2)); // pc 10,11
    }

    #[test]
    fn syscall_call_does_not_push_a_frame() {
        // call@pc1 whose next PC is pc2 == pc1+1 is a syscall, not a local call.
        let mut insns = vec![insn(ebpf::MOV64_IMM); 3];
        insns[1] = insn(ebpf::CALL_IMM);
        let trace = [0usize, 1, 2];

        let folded = fold_trace(&trace, &insns, label_two);
        assert_eq!(folded, vec![("main".to_string(), 3)]);
    }

    #[test]
    fn symbolicate_reads_real_sidecar() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../tests/fixtures/counter_with_helper.debug"
        );
        let syms = SymbolIndex::from_path(path).expect("load sidecar");
        // lddw-free fixture, so logical == slot; identity PcMap over 9 slots.
        let insns: Vec<ebpf::Insn> = vec![insn(ebpf::MOV64_IMM); 9];
        let map = PcMap::from_insns(&insns);

        let steps = symbolicate_trace(&[0, 4], &syms, &map);
        assert_eq!(steps[0].function, "increment_by");
        assert_eq!(steps[1].function, "entrypoint");
        assert_eq!(
            steps[0].inline.first().map(String::as_str),
            Some("increment_by")
        );
    }
}
