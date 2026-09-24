use serde::Serialize;

/// Generation outcome, never a claim that Lean has checked the artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum RefinementOutcome {
    NotRequested,
    Emitted,
    Rejected {
        reason: RefinementReason,
        message: String,
    },
    Unsupported {
        reason: RefinementReason,
        message: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum RefinementReason {
    MissingLayout,
    InvalidLayout,
    MissingField,
    UnsupportedOperation,
    MutationNotFound,
    MutationMismatch,
    MissingParameterBinding,
    InvalidParameterBinding,
    ParameterMismatch,
    UnsupportedShape,
    UnregisteredArm,
}

impl RefinementOutcome {
    pub(crate) fn rejected(reason: RefinementReason, message: impl Into<String>) -> Self {
        Self::Rejected {
            reason,
            message: message.into(),
        }
    }

    pub(crate) fn unsupported(reason: RefinementReason, message: impl Into<String>) -> Self {
        Self::Unsupported {
            reason,
            message: message.into(),
        }
    }
}
