//! Programmatic lifting API.

use std::path::Path;

use solana_sbpf::static_analysis::Analysis;

use crate::{
    lift_one_with_layouts, DiagnosticKind, LiftError, LiftOptions, LiftResult, ProgramImage,
};

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
}
