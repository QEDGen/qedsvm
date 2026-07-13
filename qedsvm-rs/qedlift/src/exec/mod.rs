//! Symbolic execution facade: the per-opcode `step` interpreter, the modeled-syscall
//! table and the CFG walk (`walk_and_exec`) with its retry loop and typed
//! fault terminals.

mod control;
mod step;
mod syscall_registry;
mod walk;

pub(super) use syscall_registry::{imm_is_modeled_syscall, AbortKind};
pub(super) use walk::{walk_and_exec, FaultTerminal, WalkResult};
