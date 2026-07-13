use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum DiagnosticKind {
    SyscallUnmodeled,
    SyscallUntraced,
    CallUnresolved,
    OpcodeUnmodeled,
    WalkerSteps,
    ByteAliasing,
    SymbolicOperand,
    UnsupportedConstruct,
    CuBudgetExceeded,
    WitnessFailed,
    TraceInput,
    Other,
}

impl DiagnosticKind {
    pub(super) const fn label(self) -> &'static str {
        match self {
            Self::SyscallUnmodeled => "syscall-unmodeled",
            Self::SyscallUntraced => "syscall-untraced",
            Self::CallUnresolved => "call-unresolved",
            Self::OpcodeUnmodeled => "opcode-unmodeled",
            Self::WalkerSteps => "walker-steps",
            Self::ByteAliasing => "byte-aliasing",
            Self::SymbolicOperand => "symbolic-operand",
            Self::UnsupportedConstruct => "unsupported-construct",
            Self::CuBudgetExceeded => "cu-budget-exceeded",
            Self::WitnessFailed => "witness-failed",
            Self::TraceInput => "trace-input",
            Self::Other => "other",
        }
    }
}

#[derive(Debug)]
pub(super) struct LiftError {
    kind: DiagnosticKind,
    message: String,
}

impl LiftError {
    pub(super) fn new(kind: DiagnosticKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    pub(super) fn with_context(self, context: impl fmt::Display) -> Self {
        Self::new(self.kind, format!("{context}{}", self.message))
    }

    pub(super) const fn kind(&self) -> DiagnosticKind {
        self.kind
    }
}

impl fmt::Display for LiftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for LiftError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_preserves_diagnostic_kind() {
        let error = LiftError::new(DiagnosticKind::WitnessFailed, "inner").with_context("outer: ");

        assert_eq!(error.kind(), DiagnosticKind::WitnessFailed);
        assert_eq!(error.to_string(), "outer: inner");
    }

    #[test]
    fn labels_are_stable() {
        assert_eq!(DiagnosticKind::OpcodeUnmodeled.label(), "opcode-unmodeled");
        assert_eq!(DiagnosticKind::SymbolicOperand.label(), "symbolic-operand");
        assert_eq!(DiagnosticKind::WitnessFailed.label(), "witness-failed");
    }
}
