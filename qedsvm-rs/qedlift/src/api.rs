//! Programmatic lifting API.

use std::path::Path;

use solana_sbpf::static_analysis::Analysis;

use crate::cpi_path::CpiCalleeContract;
use crate::diagnostic::{DiagnosticKind, LiftError};
use crate::lift::{lift_one_with_layouts, LiftOptions, LiftResult};
use qed_analysis::image::ProgramImage;

/// Reusable analysis session for lifting one or more paths through a program.
///
/// Constructing a session performs static analysis once. Subsequent calls to
/// [`Lifter::lift`] are in-memory: they do not parse process arguments or write
/// generated modules to disk.
pub struct Lifter<'a> {
    program_path: &'a Path,
    program: &'a ProgramImage,
    analysis: Analysis<'a>,
}

impl<'a> Lifter<'a> {
    /// Analyze a loaded program image and prepare it for repeated lifts.
    ///
    /// `program_path` is provenance used in the generated Lean module and for
    /// deriving its default name; the program bytes come from `program`.
    pub fn new(program_path: &'a Path, program: &'a ProgramImage) -> Result<Self, LiftError> {
        let analysis = Analysis::from_executable(&program.executable).map_err(|error| {
            LiftError::new(
                DiagnosticKind::Other,
                format!("qedlift: failed to analyze program: {error}"),
            )
        })?;
        Ok(Self {
            program_path,
            program,
            analysis,
        })
    }

    pub(crate) fn from_analysis(
        program_path: &'a Path,
        program: &'a ProgramImage,
        analysis: Analysis<'a>,
    ) -> Self {
        Self {
            program_path,
            program,
            analysis,
        }
    }

    /// Lift one selected path and return generated modules in memory.
    pub fn lift(&self, options: LiftOptions<'_>) -> Result<LiftResult, LiftError> {
        lift_one_with_layouts(self.program_path, self.program, &self.analysis, options)
    }

    /// Lift a caller path across one CPI. `prefix` selects the path up to the
    /// invoke (it must end at a `sol_invoke_signed` terminal); each suffix is
    /// a caller-only trace starting right after the invoke (callee PCs
    /// removed). `contract` states what the callee may do to caller memory.
    /// Returns the prefix lift plus, per suffix, a module holding
    /// the suffix triple and the composed `_cpi_path` theorem. `prefix_import`
    /// is the Lean import path of the prefix module.
    pub fn lift_cpi_paths(
        &self,
        prefix: LiftOptions<'_>,
        prefix_import: &str,
        contract: &CpiCalleeContract,
        suffixes: &[CpiSuffix<'_>],
    ) -> Result<(LiftResult, Vec<CpiPathModule>), LiftError> {
        let prefix_result = self.lift(prefix)?;
        let invoke_pc = prefix_result.path.exit_pc;
        let mut modules = Vec::with_capacity(suffixes.len());
        for suffix in suffixes {
            if suffix.trace.first() != Some(&(invoke_pc + 1)) {
                return Err(LiftError::new(
                    DiagnosticKind::TraceInput,
                    format!(
                        "qedlift: CPI suffix {:?} trace must start at pc {}",
                        suffix.name,
                        invoke_pc + 1
                    ),
                ));
            }
            let module_name = format!("{}{}", prefix_result.module_name, suffix.name);
            let lifted = self.lift(LiftOptions {
                trace: Some(suffix.trace),
                arm_entry: Some(invoke_pc + 1),
                module_override: Some(module_name.clone()),
                ..LiftOptions::default()
            })?;
            let lean = crate::cpi_path::compose(
                &prefix_result.path,
                prefix_import,
                &lifted.path,
                &lifted.lean,
                suffix.name,
                contract,
            )?;
            modules.push(CpiPathModule { module_name, lean });
        }
        Ok((prefix_result, modules))
    }
}

/// One post-CPI continuation to compose onto a CPI prefix.
pub struct CpiSuffix<'t> {
    /// Name suffix for the generated module, e.g. `"Success"`.
    pub name: &'t str,
    /// Caller-only logical-PC trace starting right after the invoke.
    pub trace: &'t [usize],
}

/// Generated suffix module carrying the composed `_cpi_path` theorem.
pub struct CpiPathModule {
    pub module_name: String,
    pub lean: String,
}
