//! qedlift — takes a compiled `.so`, symbolically executes the decoded eBPF,
//! and emits a Lean `cuTripleWithinMem` Hoare triple with pre/post conditions
//! derived from the execution, discharged by `sl_block_auto`. Also emits
//! asm-refines theorems for known program shapes.

use solana_sbpf::static_analysis::Analysis;

mod api;
mod branch;
mod core;
mod diagnostic;
mod driver;
mod emit;
mod exec;
mod input;
mod isa;
mod lift;
mod refinement;
mod render;
mod spec_call;
mod state;
mod syscalls;
mod transition;
mod witness;

pub use api::Lifter;
pub use diagnostic::{DiagnosticKind, LiftError};
use input::{load_binary, load_descriptor, load_idl_value, load_trace, parse_args, Command};
#[cfg(test)]
use input::{load_qedmeta, sidecar_account_layouts};

#[cfg(test)]
use driver::run_transition;
use driver::{
    run_batch_mode, run_coverage_mode, run_profile_mode, run_qedmeta_mode, run_single_mode,
    run_transition_mode,
};
#[cfg(test)]
use lift::lift_one;
#[cfg(test)]
use lift::{lift_one_with_layouts, LiftRequest};
pub use lift::{LiftOptions, LiftResult};
pub use qed_analysis::{image::ProgramImage, layout::AccountLayout};
pub use qed_artifacts::RefinementDescriptor;

#[cfg(test)]
mod tests;

/// Run the qedlift command using process arguments.
pub fn run() -> Result<(), Box<dyn std::error::Error>> {
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

    match &args.command {
        Command::Profile => run_profile_mode(&args, &ctx, trace.as_deref()),
        Command::Coverage => run_coverage_mode(&args, &ctx, &analysis),
        Command::Transition => run_transition_mode(
            &args,
            &ctx,
            &analysis,
            descriptor.as_ref(),
            idl_value.as_ref(),
        ),
        Command::QedMeta { path } => run_qedmeta_mode(
            &args,
            &ctx,
            &analysis,
            path.as_path(),
            trace.as_deref(),
            idl_value.as_ref(),
        ),
        Command::Batch { idl, output_dir } => run_batch_mode(
            &args,
            &ctx,
            &analysis,
            idl.as_path(),
            output_dir.as_path(),
            idl_value.as_ref(),
        ),
        Command::Single => {
            let lifter = Lifter::from_analysis(&args.so, &ctx, analysis);
            run_single_mode(
                &args,
                &lifter,
                trace.as_deref(),
                descriptor.as_ref(),
                idl_value.as_ref(),
            )
        }
    }
}
