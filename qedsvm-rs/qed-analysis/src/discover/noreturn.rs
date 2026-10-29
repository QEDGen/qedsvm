//! Panic-chain witnesses for `SVM.SBPF.noRetCheck`. A head is a function the CFG proves
//! never reaches `exit`. Its witness walks straight-line runs and local calls down to the
//! `sol_panic_` call. Steps are emitted so each one continues only at an earlier step,
//! which is the order the Lean check needs.

use crate::{
    cfg::{Cfg, Flow},
    image::ProgramImage,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum NoRetStep {
    Straight {
        pc: usize,
        len: usize,
    },
    CallLocal {
        pc: usize,
        target: usize,
    },
    /// A conditional jump; both `target` and `pc + 1` continue to a panic.
    Branch {
        pc: usize,
        target: usize,
    },
    PanicCall {
        pc: usize,
    },
}

impl NoRetStep {
    pub fn pc(&self) -> usize {
        match *self {
            NoRetStep::Straight { pc, .. }
            | NoRetStep::CallLocal { pc, .. }
            | NoRetStep::Branch { pc, .. }
            | NoRetStep::PanicCall { pc } => pc,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NoRetWitness {
    pub heads: Vec<usize>,
    pub steps: Vec<NoRetStep>,
    /// No-return functions left out, with the reason (for example a chain that ends in
    /// `abort`, which the Lean check does not model).
    pub skipped: Vec<(usize, String)>,
}

impl NoRetWitness {
    /// The witness as a Lean `NoRetWitness` literal.
    pub fn to_lean(&self) -> String {
        let heads = self
            .heads
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        let steps = self
            .steps
            .iter()
            .map(|s| match *s {
                NoRetStep::Straight { pc, len } => format!(".straight {pc} {len}"),
                NoRetStep::CallLocal { pc, target } => format!(".callLocal {pc} {target}"),
                NoRetStep::Branch { pc, target } => format!(".branch {pc} {target}"),
                NoRetStep::PanicCall { pc } => format!(".panicCall {pc}"),
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("{{ heads := [{heads}]\n    steps := [{steps}] }}")
    }
}

struct Walk<'a> {
    cfg: &'a Cfg,
    done: BTreeSet<usize>,
    active: BTreeSet<usize>,
    steps: Vec<NoRetStep>,
}

impl Walk<'_> {
    fn visit(&mut self, pc: usize) -> Result<(), String> {
        if self.done.contains(&pc) {
            return Ok(());
        }
        if !self.active.insert(pc) {
            return Err(format!("panic chain loops at {pc}"));
        }
        let flow = &self.cfg.flow;
        let len = (pc..flow.len())
            .take_while(|&p| flow[p] == Flow::Seq)
            .count();
        let step = if len > 0 {
            self.visit(pc + len)?;
            NoRetStep::Straight { pc, len }
        } else {
            match flow.get(pc) {
                Some(Flow::Call(target)) => {
                    self.visit(*target)?;
                    NoRetStep::CallLocal {
                        pc,
                        target: *target,
                    }
                }
                Some(Flow::Branch(target)) => {
                    self.visit(*target)?;
                    self.visit(pc + 1)?;
                    NoRetStep::Branch {
                        pc,
                        target: *target,
                    }
                }
                Some(Flow::Syscall {
                    name: Some("sol_panic_"),
                    ..
                }) => NoRetStep::PanicCall { pc },
                other => return Err(format!("{pc}: {other:?} before a panic call")),
            }
        };
        self.active.remove(&pc);
        self.done.insert(pc);
        self.steps.push(step);
        Ok(())
    }
}

/// The witness for every no-return function reachable from the entry. A function whose
/// chain the check cannot model goes to `skipped`; nothing is guessed.
pub fn noreturn_witness(_image: &ProgramImage, cfg: &Cfg) -> Result<NoRetWitness, String> {
    let reachable = cfg.reachable_functions();
    let mut walk = Walk {
        cfg,
        done: BTreeSet::new(),
        active: BTreeSet::new(),
        steps: Vec::new(),
    };
    let mut heads = Vec::new();
    let mut skipped = Vec::new();
    for &f in cfg.noreturn.iter().filter(|f| reachable.contains(f)) {
        let saved = (walk.done.clone(), walk.steps.len());
        match walk.visit(f) {
            Ok(()) => heads.push(f),
            Err(reason) => {
                // Drop the partial chain so the witness stays in check order.
                walk.done = saved.0;
                walk.steps.truncate(saved.1);
                walk.active.clear();
                skipped.push((f, reason));
            }
        }
    }
    Ok(NoRetWitness {
        heads,
        steps: walk.steps,
        skipped,
    })
}
