//! qedlift — takes a compiled `.so`, symbolically executes the decoded eBPF,
//! and emits a Lean `cuTripleWithinMem` Hoare triple with pre/post conditions
//! derived from the execution, discharged by `sl_block_auto`. Also emits
//! asm-refines theorems for known program shapes.

use std::path::Path;

use solana_sbpf::{
    ebpf,
    static_analysis::Analysis,
};

#[path = "qedlift/input.rs"]
mod input;
#[path = "qedlift/branch.rs"]
mod branch;
#[path = "qedlift/core.rs"]
mod core;
#[path = "qedlift/emit.rs"]
mod emit;
#[path = "qedlift/isa.rs"]
mod isa;
#[path = "qedlift/refinement.rs"]
mod refinement;
#[path = "qedlift/render.rs"]
mod render;
#[path = "qedlift/state.rs"]
mod state;
#[path = "qedlift/syscalls.rs"]
mod syscalls;
#[path = "qedlift/witness.rs"]
mod witness;
#[path = "qedlift/spec_call.rs"]
mod spec_call;
#[path = "qedlift/exec.rs"]
mod exec;
#[path = "qedlift/lift.rs"]
mod lift;
#[path = "qedlift/driver.rs"]
mod driver;

use core::{
    arsh_render, canon_addr, eval_expr, lean_off, reg_initial_name, reg_lit, Atom, Expr, Width,
};
use emit::{
    atoms_to_lean, atoms_to_lean_heap, build_sat_witness, fold_abstractions, heap_cell_addr,
    post_atoms, region_req,
};
use branch::{BranchHyp, BranchKind};
use input::{
    Args, BinaryCtx, RefinementDescriptor, load_binary, load_descriptor, load_idl,
    load_idl_value, load_qedmeta, load_trace, parse_args, pascal_case,
    sidecar_account_layouts,
};
use isa::{
    function_registry, function_registry_lean, insn_to_lean, insn_to_lean_full,
    render_callstack, resolve_call_target_logical, resolve_jump_target,
};
use refinement::{emit_descriptor_refinement, emit_refinement, emit_transition_bundle,
    emit_transition_fault, emit_transition_path, is_const_delta_arm, BItem, FaultTail,
    RefineTarget, RefinementCtx, TransitionPathInfo};
use state::SymState;
use syscalls::{
    emit_sol_create_program_address, emit_sol_get_sysvar, emit_sol_log, emit_sol_memcmp,
    emit_sol_memcpy, emit_sol_memset, emit_sol_set_return_data, emit_sol_sha256,
};
use witness::build_branch_witness;

// Re-exports of the split-out lifter stages: visible at the crate root so the
// sibling modules (and `layout_tests`' `use super::*`) resolve them here.
use driver::{run_batch_mode, run_coverage_mode, run_profile_mode, run_qedmeta_mode, run_single_mode, run_transition_mode};
#[cfg(test)]
use driver::run_transition;
use exec::{imm_is_modeled_syscall, walk_and_exec, AbortKind, FaultTerminal, WalkResult};
use lift::{lift_one_with_layouts, LiftOutput};
#[cfg(test)]
use lift::lift_one;
use spec_call::{spec_call_for, SpecCall};
use qed_analysis::layout::AccountLayout;
use qed_analysis::symbolicate::SymbolIndex;
use qed_analysis::profile::{fold_trace, folded_lines, symbolicate_trace};

#[cfg(test)]
#[path = "qedlift/tests.rs"]
mod layout_tests;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = parse_args().map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

    // Load once: amortises parse+CFG build across batch arms (~28 arms × ~10s → a few ms each).
    let ctx = load_binary(&args.so)?;
    let analysis = Analysis::from_executable(&ctx.executable)?;

    let idl_value = args.idl.as_ref().and_then(|p| load_idl_value(p));

    let trace: Option<Vec<usize>> = match args.trace.as_ref() {
        Some(p) => Some(load_trace(p)?),
        None => None,
    };

    // Spec-driven refinement descriptor (single-arm only). The seam to qedspec.
    let descriptor: Option<RefinementDescriptor> = match args.descriptor.as_ref() {
        Some(p) => Some(load_descriptor(p)?),
        None => None,
    };

    if args.profile {
        return run_profile_mode(&args, &ctx, trace.as_deref());
    }
    if args.coverage {
        return run_coverage_mode(&args, &ctx, &analysis);
    }
    if args.transition {
        return run_transition_mode(&args, &ctx, &analysis,
            descriptor.as_ref(), idl_value.as_ref());
    }
    if let Some(meta_path) = args.qedmeta.as_ref() {
        return run_qedmeta_mode(&args, &ctx, &analysis, meta_path,
            trace.as_deref(), idl_value.as_ref());
    }
    // Batch mode: --idl + --output-dir. Without --output-dir falls through to single-arm.
    if let (Some(idl_path), Some(output_dir)) =
        (args.idl.as_ref(), args.output_dir.as_ref())
    {
        return run_batch_mode(&args, &ctx, &analysis, idl_path, output_dir,
            idl_value.as_ref());
    }
    run_single_mode(&args, &ctx, &analysis, trace.as_deref(),
        descriptor.as_ref(), idl_value.as_ref())
}
