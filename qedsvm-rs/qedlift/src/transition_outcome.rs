//! Machine-readable `--transition` outcome (#70).
//!
//! `--transition` prints one `transition outcome: {json}` line on stderr,
//! the transition-mode counterpart of the single-path `refinement outcome:`
//! line. It carries, per discovered `<stem>_<label>.pcs` path, the kind the
//! emitter decided (a clean return with its exit code, or a typed VM fault)
//! or why the path was not emitted, so callers never parse the Lean.
//! Like `RefinementOutcome`, it is a generation outcome: Lean has not
//! checked the artifacts yet.

use serde::Serialize;

use crate::refinement::RefinementReason;

/// Bumped on any breaking change to the JSON shape.
pub const TRANSITION_OUTCOME_SCHEMA: u32 = 1;

/// The typed VM error a fault path ends in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VmErrorKind {
    Abort,
    AccessViolation,
}

impl VmErrorKind {
    /// The `SVM.SBPF.VmError` constructor the fault corollary states.
    pub(crate) fn lean_ctor(self) -> &'static str {
        match self {
            VmErrorKind::Abort => ".abort",
            VmErrorKind::AccessViolation => ".accessViolation",
        }
    }
}

/// How one emitted path ends. A spec rejection (`requires C else E`) is
/// usually a `Return` with a non-zero exit code and no tracked write, not a
/// `Fault`, so the two stay distinct.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PathKind {
    Return {
        /// `None` when r0 at `.exit` is not a constant; such a path is
        /// reported `unsupported` (`symbolic_exit_code`), never emitted.
        #[serde(skip_serializing_if = "Option::is_none")]
        exit_code: Option<u64>,
        /// Whether the path performs the descriptor's tracked-field write.
        tracked_written: bool,
    },
    Fault {
        vm_error: VmErrorKind,
    },
}

impl PathKind {
    /// The `SVM.Solana.Abstract` predicate the path corollary proves.
    pub(crate) fn pred(&self) -> &'static str {
        match self {
            PathKind::Return { .. } => "AsmRefinesTransitionPath",
            PathKind::Fault { .. } => "AsmRefinesTransitionFault",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum OutcomeStatus {
    Emitted,
    Rejected,
    Unsupported,
}

/// Why a path (or the whole run) was not emitted: a refinement reason when
/// the descriptor refinement explains it, else a transition-only reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub enum TransitionReason {
    Refinement(RefinementReason),
    Transition(TransitionOnlyReason),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TransitionOnlyReason {
    /// Fewer than two `<stem>_<label>.pcs` traces beside the .so.
    TooFewTraces,
    /// A discovered trace could not be read.
    TraceUnreadable,
    /// The lift itself failed before any transition codegen.
    LiftFailed,
    /// A framed tracked-field name collides with a binder of the lift.
    BinderConflict,
    /// A return path whose exit code is not a constant.
    SymbolicExitCode,
    /// Every path emitted, but the bundle theorem did not.
    BundleFailed,
}

impl From<RefinementReason> for TransitionReason {
    fn from(r: RefinementReason) -> Self {
        TransitionReason::Refinement(r)
    }
}

impl From<TransitionOnlyReason> for TransitionReason {
    fn from(r: TransitionOnlyReason) -> Self {
        TransitionReason::Transition(r)
    }
}

/// One discovered path.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PathOutcome {
    /// The `<label>` of the `<stem>_<label>.pcs` trace.
    pub label: String,
    pub module: String,
    pub status: OutcomeStatus,
    #[serde(flatten, skip_serializing_if = "Option::is_none")]
    pub kind: Option<PathKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<TransitionReason>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

impl PathOutcome {
    pub(crate) fn emitted(label: &str, module: &str, kind: PathKind) -> Self {
        Self {
            label: label.to_string(),
            module: module.to_string(),
            status: OutcomeStatus::Emitted,
            kind: Some(kind),
            reason: None,
            message: None,
        }
    }

    pub(crate) fn from_failure(label: &str, module: &str, f: TransitionFailure) -> Self {
        Self::failed(label, module, f.status, f.reason, f.message)
    }

    pub(crate) fn failed(
        label: &str,
        module: &str,
        status: OutcomeStatus,
        reason: TransitionReason,
        message: impl Into<String>,
    ) -> Self {
        Self {
            label: label.to_string(),
            module: module.to_string(),
            status,
            kind: None,
            reason: Some(reason),
            message: Some(message.into()),
        }
    }
}

/// Why the transition emitter fell closed on one path (or on the bundle).
/// `rejected` means the binary disagrees with the descriptor; `unsupported`
/// means the shape is outside what the emitter wires.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TransitionFailure {
    pub(crate) status: OutcomeStatus,
    pub(crate) reason: TransitionReason,
    pub(crate) message: String,
}

impl TransitionFailure {
    pub(crate) fn rejected(
        reason: impl Into<TransitionReason>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            status: OutcomeStatus::Rejected,
            reason: reason.into(),
            message: message.into(),
        }
    }

    pub(crate) fn unsupported(
        reason: impl Into<TransitionReason>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            status: OutcomeStatus::Unsupported,
            reason: reason.into(),
            message: message.into(),
        }
    }
}

impl std::fmt::Display for TransitionFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// The whole `--transition` run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TransitionOutcome {
    pub schema: u32,
    pub status: OutcomeStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bundle: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<TransitionReason>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    pub paths: Vec<PathOutcome>,
}

impl TransitionOutcome {
    /// A run-level failure (no bundle).
    pub(crate) fn failed(
        status: OutcomeStatus,
        reason: TransitionReason,
        message: impl Into<String>,
        paths: Vec<PathOutcome>,
    ) -> Self {
        Self {
            schema: TRANSITION_OUTCOME_SCHEMA,
            status,
            bundle: None,
            reason: Some(reason),
            message: Some(message.into()),
            paths,
        }
    }

    /// Roll per-path results up: `rejected` if any path was rejected (the
    /// binary disagrees with the descriptor), else `unsupported`.
    pub(crate) fn from_failed_paths(paths: Vec<PathOutcome>) -> Self {
        let status = if paths.iter().any(|p| p.status == OutcomeStatus::Rejected) {
            OutcomeStatus::Rejected
        } else {
            OutcomeStatus::Unsupported
        };
        let n = paths
            .iter()
            .filter(|p| p.status != OutcomeStatus::Emitted)
            .count();
        Self {
            schema: TRANSITION_OUTCOME_SCHEMA,
            status,
            bundle: None,
            reason: None,
            message: Some(format!("{n} of {} paths not emitted", paths.len())),
            paths,
        }
    }

    pub(crate) fn emitted(bundle: &str, paths: Vec<PathOutcome>) -> Self {
        Self {
            schema: TRANSITION_OUTCOME_SCHEMA,
            status: OutcomeStatus::Emitted,
            bundle: Some(bundle.to_string()),
            reason: None,
            message: None,
            paths,
        }
    }
}
