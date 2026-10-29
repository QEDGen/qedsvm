//! Instructions and success edges from the dispatcher (solana-skills#450).
//!
//! For each loop-free success edge, the accounts are walked in order. Each account's data
//! length is taken from a check the program makes on every path to the edge
//! (`data_len == c`), or assumed to be 0 when the program makes none. Both kinds become
//! visible hypotheses of the generated theorem (`LenStatus`). With the lengths fixed, the
//! instruction data has a fixed offset, and a branch that compares its first byte with a
//! constant is a dispatch arm. Arms with the same constant are one instruction.

use crate::{
    cfg::{Cfg, Flow},
    concept_map::ConceptMap,
    discover::noreturn::noreturn_witness,
    image::ProgramImage,
    input_layout::aligned_input_offsets,
    success_proofs::{
        provenance::{abstract_map_with, AState, AVal, Assumed, Width},
        Graph,
    },
};
use solana_sbpf::ebpf;
use std::collections::BTreeMap;

/// Whether the program itself checks an assumed length.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LenStatus {
    /// Every path to the edge passes one of these `data_len == value` checks.
    Checked { guard_pcs: Vec<usize> },
    /// The program does not check it; the theorem assumes 0.
    Unchecked,
}

#[derive(Clone, Debug)]
pub struct EdgeLayout {
    pub edge: usize,
    pub accounts: u64,
    /// One length word per account, in account order.
    pub assumed: Vec<((u64, Width, u64), LenStatus)>,
    /// Offset of the first instruction-data byte.
    pub instruction_data: u64,
}

impl EdgeLayout {
    pub fn assumed_words(&self) -> Assumed {
        self.assumed.iter().map(|(w, _)| *w).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub name: String,
    /// The concept-map function ID the name came from.
    pub function_id: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unsupported {
    /// A path from the entry to the edge goes through a cycle.
    Loop,
    /// The account count or the discriminator offset is not fixed on this edge.
    UnpinnedDiscriminator(String),
    /// No dispatch arm reaches the edge, or the arms do not cut every path to it.
    NoDispatch,
}

#[derive(Clone, Debug)]
pub struct Instruction {
    pub discriminator: u64,
    /// Dispatch-arm PCs: the first PC that only this discriminator reaches.
    pub routes: Vec<usize>,
    pub handler: Option<Label>,
    pub success_edges: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct Dispatch {
    pub instructions: Vec<Instruction>,
    pub layouts: Vec<EdgeLayout>,
    pub unsupported: Vec<(usize, Unsupported)>,
}

pub(crate) struct Analysis {
    pub(crate) graph: Graph,
}

impl Analysis {
    pub(crate) fn new(image: &ProgramImage, cfg: &Cfg) -> Result<Self, String> {
        let noret = noreturn_witness(image, cfg)?.heads;
        Ok(Self {
            graph: Graph::new(cfg, &noret)?,
        })
    }

    /// PCs on some path from the entry to `edge`.
    fn on_path(&self, cfg: &Cfg, edge: usize) -> Vec<bool> {
        let fwd = self.graph.reach(cfg.entry, &[], false);
        let back = self.graph.reach(edge, &[], true);
        fwd.iter().zip(&back).map(|(a, b)| *a && *b).collect()
    }

    fn has_cycle(&self, on: &[bool], start: usize) -> bool {
        // Iterative three-color DFS over the PCs on a path.
        let mut color = vec![0u8; on.len()];
        let mut stack = vec![(start, 0usize)];
        color[start] = 1;
        while let Some((pc, i)) = stack.pop() {
            let succ = &self.graph.succ[pc];
            if i < succ.len() {
                stack.push((pc, i + 1));
                let q = succ[i];
                if q < on.len() && on[q] {
                    match color[q] {
                        1 => return true,
                        0 => {
                            color[q] = 1;
                            stack.push((q, 0));
                        }
                        _ => {}
                    }
                }
            } else {
                color[pc] = 2;
            }
        }
        false
    }

    /// Whether `edge` is unreachable once each listed guard may only take its other side.
    fn cut_by(&self, cfg: &Cfg, edge: usize, guards: &[(usize, usize)]) -> bool {
        let mut seen = vec![false; self.graph.succ.len()];
        let mut work = vec![cfg.entry];
        while let Some(pc) = work.pop() {
            if seen[pc] {
                continue;
            }
            seen[pc] = true;
            for &q in &self.graph.succ[pc] {
                if !guards.contains(&(pc, q)) {
                    work.push(q);
                }
            }
        }
        !seen[edge]
    }
}

/// `(constant, side that requires equality)` for `jeq/jne dst, imm`.
fn equality_side(image: &ProgramImage, cfg: &Cfg, pc: usize) -> Option<(u64, usize)> {
    let i = &image.insns[pc];
    let Flow::Branch(target) = cfg.flow[pc] else {
        return None;
    };
    if i.opc & ebpf::BPF_X != 0 {
        return None;
    }
    match i.opc & 0xf0 {
        ebpf::BPF_JEQ => Some((i.imm as u64, target)),
        ebpf::BPF_JNE => Some((i.imm as u64, pc + 1)),
        _ => None,
    }
}

fn dst_val<'a>(map: &'a [Option<AState>], image: &ProgramImage, pc: usize) -> Option<&'a AVal> {
    map[pc]
        .as_ref()
        .map(|a| &a.regs[image.insns[pc].dst as usize])
}

/// The value every path to `edge` checks `word` against, with the checking guards.
fn checked_value(
    an: &Analysis,
    image: &ProgramImage,
    cfg: &Cfg,
    map: &[Option<AState>],
    on: &[bool],
    edge: usize,
    word: &AVal,
) -> Result<Option<(u64, Vec<usize>)>, String> {
    let mut found: BTreeMap<u64, Vec<(usize, usize)>> = BTreeMap::new();
    for pc in (0..on.len()).filter(|&pc| on[pc]) {
        if dst_val(map, image, pc) != Some(word) {
            continue;
        }
        if let Some((value, side)) = equality_side(image, cfg, pc) {
            found.entry(value).or_default().push((pc, side));
        }
    }
    let cutting: Vec<_> = found
        .into_iter()
        .filter(|(_, sides)| an.cut_by(cfg, edge, sides))
        .collect();
    match cutting.as_slice() {
        [] => Ok(None),
        [(value, sides)] => Ok(Some((*value, sides.iter().map(|(pc, _)| *pc).collect()))),
        _ => Err(format!("edge {edge}: conflicting checks on {word:?}")),
    }
}

pub(crate) fn layout_with(
    an: &Analysis,
    image: &ProgramImage,
    cfg: &Cfg,
    edge: usize,
) -> Result<EdgeLayout, Unsupported> {
    let on = an.on_path(cfg, edge);
    let unpinned = |m: String| Unsupported::UnpinnedDiscriminator(m);
    let map0 = abstract_map_with(image, cfg, &an.graph.succ, cfg.entry, &[]).map_err(unpinned)?;
    // The count only decides which length words to assume; the Lean pins are about what
    // the code itself reads, so a check on the low byte (p_token's `*input == 3`) is enough.
    let mut accounts = None;
    for word in [AVal::InLoad("dword", 0), AVal::InLoad("byte", 0)] {
        if let Some((value, _)) =
            checked_value(an, image, cfg, &map0, &on, edge, &word).map_err(unpinned)?
        {
            accounts = Some(value);
            break;
        }
    }
    let accounts = accounts
        .ok_or_else(|| unpinned(format!("edge {edge}: the account count is not checked")))?;
    let mut assumed = Vec::new();
    let mut lengths = Vec::new();
    for i in 0..accounts as usize {
        let mut probe = lengths.clone();
        probe.push(0);
        let offsets = aligned_input_offsets(&probe).map_err(|e| unpinned(e.to_string()))?;
        let word_off = offsets.account_data[i] as u64 - 8;
        let asm: Assumed = assumed.iter().map(|(w, _)| *w).collect();
        let map =
            abstract_map_with(image, cfg, &an.graph.succ, cfg.entry, &asm).map_err(unpinned)?;
        let word = AVal::InLoad("dword", word_off);
        let (value, status) =
            match checked_value(an, image, cfg, &map, &on, edge, &word).map_err(unpinned)? {
                Some((value, guard_pcs)) => (value, LenStatus::Checked { guard_pcs }),
                None => (0, LenStatus::Unchecked),
            };
        lengths.push(value as usize);
        assumed.push(((word_off, Width::Dword, value), status));
    }
    let offsets = aligned_input_offsets(&lengths).map_err(|e| unpinned(e.to_string()))?;
    Ok(EdgeLayout {
        edge,
        accounts,
        assumed,
        instruction_data: offsets.instruction_data as u64,
    })
}

/// The input layout a run reaching `edge` must have.
pub fn edge_layout(image: &ProgramImage, cfg: &Cfg, edge: usize) -> Result<EdgeLayout, String> {
    let an = Analysis::new(image, cfg)?;
    layout_with(&an, image, cfg, edge).map_err(|u| format!("{u:?}"))
}

/// The first function, along the arm, of an inline chain that the dispatch branch is not
/// inside. The arm's first PCs often still belong to the dispatcher, so this walks on.
fn handler_label(an: &Analysis, map: &ConceptMap, guard_pc: usize, arm: usize) -> Option<Label> {
    let chain_at = |pc: usize| -> Option<&Vec<String>> {
        let chains: Vec<_> = map
            .lines
            .iter()
            .filter(|l| l.range.start <= pc && pc < l.range.end)
            .flat_map(|l| &l.inline_chains)
            .collect();
        match chains.as_slice() {
            [one] => Some(*one),
            _ => None,
        }
    };
    let outer = chain_at(guard_pc)?;
    let mut seen = std::collections::BTreeSet::new();
    let mut queue = std::collections::VecDeque::from([arm]);
    while let Some(pc) = queue.pop_front() {
        if seen.len() > 256 || !seen.insert(pc) {
            continue;
        }
        if let Some(id) = chain_at(pc).and_then(|c| c.iter().find(|id| !outer.contains(id))) {
            let name = map.functions.iter().find(|f| &f.id == id)?.name.clone()?;
            return Some(Label {
                name,
                function_id: id.clone(),
            });
        }
        queue.extend(an.graph.succ[pc].iter().copied());
    }
    None
}

/// Every instruction the dispatcher exposes on loop-free success edges.
pub fn discover_instructions(
    image: &ProgramImage,
    cfg: &Cfg,
    concepts: Option<&ConceptMap>,
) -> Result<Dispatch, String> {
    let an = Analysis::new(image, cfg)?;
    let mut by_disc: BTreeMap<u64, Instruction> = BTreeMap::new();
    let mut layouts = Vec::new();
    let mut unsupported = Vec::new();
    for edge in cfg.outcomes(image).success_edges() {
        let on = an.on_path(cfg, edge);
        if an.has_cycle(&on, cfg.entry) {
            unsupported.push((edge, Unsupported::Loop));
            continue;
        }
        let layout = match layout_with(&an, image, cfg, edge) {
            Ok(layout) => layout,
            Err(u) => {
                unsupported.push((edge, u));
                continue;
            }
        };
        let map = abstract_map_with(
            image,
            cfg,
            &an.graph.succ,
            cfg.entry,
            &layout.assumed_words(),
        )?;
        let disc = AVal::InLoad("byte", layout.instruction_data);
        let mut arms: Vec<(u64, usize, usize)> = Vec::new();
        for pc in (0..on.len()).filter(|&pc| on[pc]) {
            if dst_val(&map, image, pc) != Some(&disc) {
                continue;
            }
            if let Some((value, side)) = equality_side(image, cfg, pc) {
                if on[side] {
                    arms.push((value, pc, side));
                }
            }
        }
        let stops: Vec<usize> = arms.iter().map(|&(_, _, arm)| arm).collect();
        if arms.is_empty() || an.graph.reach(cfg.entry, &stops, false)[edge] {
            unsupported.push((edge, Unsupported::NoDispatch));
            continue;
        }
        for (value, guard_pc, arm) in arms {
            let ix = by_disc.entry(value).or_insert_with(|| Instruction {
                discriminator: value,
                routes: Vec::new(),
                handler: concepts.and_then(|m| handler_label(&an, m, guard_pc, arm)),
                success_edges: Vec::new(),
            });
            if !ix.routes.contains(&arm) {
                ix.routes.push(arm);
            }
            if !ix.success_edges.contains(&edge) {
                ix.success_edges.push(edge);
            }
        }
        layouts.push(layout);
    }
    let mut instructions: Vec<_> = by_disc.into_values().collect();
    for ix in &mut instructions {
        ix.routes.sort_unstable();
        ix.success_edges.sort_unstable();
    }
    Ok(Dispatch {
        instructions,
        layouts,
        unsupported,
    })
}
