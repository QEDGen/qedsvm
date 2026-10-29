//! The bindings file `qed-discover` writes (solana-skills#450): everything the success-proof
//! generator needs, discovered from the binary pair. All of it is untrusted. The generated
//! Lean re-checks every PC, guard and pin against the decoded program; names are labels.

use crate::{
    cfg::Cfg,
    concept_map::ConceptMap,
    discover::{
        authority::{regions, route_authority, KeyCompare},
        dispatch::{discover_instructions, Analysis, LenStatus, Unsupported},
        fields::{label_fields, LabelStatus},
        noreturn::{noreturn_witness, NoRetWitness},
    },
    image::ProgramImage,
    success_proofs::provenance::{abstract_map_with, AVal},
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use solana_sbpf::ebpf;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AssumedWord {
    /// Input offset of an account's `data_len` word.
    pub offset: u64,
    pub value: u64,
    /// The program checks `data_len == value` on every path to the edge.
    pub checked: bool,
    pub guard_pcs: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct KeyCompareBinding {
    pub account: usize,
    pub against_account: usize,
    pub against_data_offset: u64,
}

impl From<KeyCompare> for KeyCompareBinding {
    fn from(k: KeyCompare) -> Self {
        Self {
            account: k.account,
            against_account: k.against_account,
            against_data_offset: k.against_data_offset,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RouteBinding {
    /// The route checkpoint: a dispatch arm.
    pub pc: usize,
    pub discriminator: u64,
    pub signers: Vec<usize>,
    pub key_compares: Vec<KeyCompareBinding>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FieldBinding {
    pub account: usize,
    pub data_offset: u64,
    pub width: u64,
    /// A DWARF member name; `None` when the label is refused.
    pub name: Option<String>,
    pub structure: Option<String>,
    pub refused: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EdgeBinding {
    pub pc: usize,
    pub accounts: u64,
    pub assumed: Vec<AssumedWord>,
    pub instruction_data: u64,
    /// Accounts whose duplicate marker every path checks.
    pub non_duplicate: Vec<usize>,
    pub routes: Vec<RouteBinding>,
    pub fields: Vec<FieldBinding>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InstructionBinding {
    pub discriminator: u64,
    pub handler: Option<String>,
    pub routes: Vec<usize>,
    pub success_edges: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UnsupportedEdge {
    pub pc: usize,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Bindings {
    pub schema_version: u32,
    pub trust: String,
    pub artifact_sha256: String,
    pub debug_sha256: String,
    pub entry: usize,
    pub noreturn: NoRetWitness,
    pub instructions: Vec<InstructionBinding>,
    pub edges: Vec<EdgeBinding>,
    pub unsupported: Vec<UnsupportedEdge>,
    pub diagnostics: Vec<String>,
}

impl Bindings {
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    pub fn from_json(text: &str) -> Result<Self, String> {
        let b: Bindings = serde_json::from_str(text).map_err(|e| e.to_string())?;
        if b.schema_version != 1 {
            return Err(format!("unsupported bindings schema {}", b.schema_version));
        }
        Ok(b)
    }
}

fn unsupported_reason(u: &Unsupported) -> String {
    match u {
        Unsupported::Loop => "loop".into(),
        Unsupported::UnpinnedDiscriminator(m) => format!("unpinned discriminator: {m}"),
        Unsupported::NoDispatch => "no dispatch arm cuts the paths to this edge".into(),
    }
}

/// Discover bindings for `deployed`, labelled from `map`. `map` must describe `deployed`.
pub fn discover(deployed: &[u8], map: &ConceptMap) -> Result<Bindings, String> {
    let sha = format!("{:x}", Sha256::digest(deployed));
    if map.artifact.deployed_sha256 != sha {
        return Err(format!(
            "concept map describes {}, not this artifact ({sha})",
            map.artifact.deployed_sha256
        ));
    }
    let image = ProgramImage::from_elf_bytes(deployed)?;
    let cfg = Cfg::build(&image)?;
    let an = Analysis::new(&image, &cfg)?;
    let noreturn = noreturn_witness(&image, &cfg)?;
    let dispatch = discover_instructions(&image, &cfg, Some(map))?;
    let mut diagnostics: Vec<String> = noreturn
        .skipped
        .iter()
        .map(|(pc, why)| format!("no-return helper {pc} left out: {why}"))
        .collect();
    let mut edges = Vec::new();
    for layout in &dispatch.layouts {
        let map_abs = abstract_map_with(
            &image,
            &cfg,
            &an.graph.succ,
            cfg.entry,
            &layout.assumed_words(),
        )?;
        let regions = regions(layout)?;
        let mut guards = an.graph.guards(&cfg, cfg.entry, layout.edge);
        let mut routes = Vec::new();
        for ix in &dispatch.instructions {
            for &r in &ix.routes {
                if !an.graph.reach(r, &[], false)[layout.edge] {
                    continue;
                }
                let a = route_authority(&image, &cfg, layout, r)?;
                routes.push(RouteBinding {
                    pc: r,
                    discriminator: ix.discriminator,
                    signers: a.signers,
                    key_compares: a.key_compares.into_iter().map(Into::into).collect(),
                });
                guards.extend(an.graph.guards(&cfg, r, layout.edge));
            }
        }
        routes.sort_by_key(|r| r.pc);
        let dom = an.graph.guards(&cfg, cfg.entry, layout.edge);
        let mut non_duplicate = BTreeSet::new();
        let mut loads: Vec<BTreeSet<(u64, u64)>> = vec![BTreeSet::new(); regions.len()];
        for (gi, g) in guards.iter().enumerate() {
            let (Some(a), i) = (&map_abs[g.pc], &image.insns[g.pc]) else {
                continue;
            };
            let mut ops = vec![a.regs[i.dst as usize].clone()];
            if i.opc & ebpf::BPF_X != 0 {
                ops.push(a.regs[i.src as usize].clone());
            }
            for op in ops {
                let AVal::InLoad(w, off) = op else { continue };
                let width = match w {
                    "byte" => 1,
                    "half" => 2,
                    "word" => 4,
                    _ => 8,
                };
                for (n, &(header, data, len)) in regions.iter().enumerate() {
                    if gi < dom.len() && off == header {
                        non_duplicate.insert(n);
                    }
                    if off >= data && off + width <= data + len {
                        loads[n].insert((off - data, width));
                    }
                }
            }
        }
        let mut fields = Vec::new();
        for (n, set) in loads.iter().enumerate() {
            if set.is_empty() {
                continue;
            }
            let list: Vec<_> = set.iter().copied().collect();
            for l in label_fields(map, regions[n].2, &list) {
                let (structure, refused) = match l.status {
                    LabelStatus::Labelled { structure_id } => (Some(structure_id), None),
                    LabelStatus::Refused(why) => (None, Some(why)),
                };
                if let Some(why) = &refused {
                    let d = format!("edge {}: account {n} labels refused: {why}", layout.edge);
                    if !diagnostics.contains(&d) {
                        diagnostics.push(d);
                    }
                }
                fields.push(FieldBinding {
                    account: n,
                    data_offset: l.data_offset,
                    width: l.width,
                    name: l.name,
                    structure,
                    refused,
                });
            }
        }
        edges.push(EdgeBinding {
            pc: layout.edge,
            accounts: layout.accounts,
            assumed: layout
                .assumed
                .iter()
                .map(|((offset, _, value), status)| AssumedWord {
                    offset: *offset,
                    value: *value,
                    checked: matches!(status, LenStatus::Checked { .. }),
                    guard_pcs: match status {
                        LenStatus::Checked { guard_pcs } => guard_pcs.clone(),
                        LenStatus::Unchecked => vec![],
                    },
                })
                .collect(),
            instruction_data: layout.instruction_data,
            non_duplicate: non_duplicate.into_iter().collect(),
            routes,
            fields,
        });
    }
    Ok(Bindings {
        schema_version: 1,
        trust: "untrusted_discovered_bindings".into(),
        artifact_sha256: sha,
        debug_sha256: map.artifact.debug_sha256.clone(),
        entry: cfg.entry,
        noreturn,
        instructions: dispatch
            .instructions
            .iter()
            .map(|ix| InstructionBinding {
                discriminator: ix.discriminator,
                handler: ix.handler.as_ref().map(|l| l.name.clone()),
                routes: ix.routes.clone(),
                success_edges: ix.success_edges.clone(),
            })
            .collect(),
        edges,
        unsupported: dispatch
            .unsupported
            .iter()
            .map(|(pc, u)| UnsupportedEdge {
                pc: *pc,
                reason: unsupported_reason(u),
            })
            .collect(),
        diagnostics,
    })
}
