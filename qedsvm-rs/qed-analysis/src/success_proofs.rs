//! Untrusted, deterministic producers for the existing p-token success certificates.
//!
//! Inputs select coverage; they are never proof assumptions. The emitted `native_decide`
//! obligations still check the decoded instructions, route cuts, guard directions,
//! abstract post-fixpoint and input pins using the generic Lean checkers.

mod provenance;

use std::collections::BTreeSet;
use std::fmt::Write;

use serde::Deserialize;
use sha2::{Digest, Sha256};
use solana_sbpf::{ebpf, program::SBPFVersion};

use crate::{
    cfg::{Cfg, Flow},
    image::ProgramImage,
};
use provenance::{abstract_map, AVal};

/// Versioned, artifact-bound temporary manual bindings, replaceable by discovered bindings.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BaselineInputs {
    pub schema_version: u32,
    pub artifact_sha256: String,
    pub entry: usize,
    pub noreturn: Vec<usize>,
    pub guard_pins: Vec<GuardPin>,
    pub edges: Vec<EdgeInput>,
    /// Readable field bindings consumed by the authored TransferSpec, not proof facts.
    pub readable_fields: Vec<ReadableField>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GuardPin {
    pub edge: usize,
    pub pc: usize,
    pub on_success: usize,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EdgeInput {
    pub pc: usize,
    pub description: String,
    pub input_description: String,
    pub checkpoints: Vec<usize>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReadableField {
    pub name: String,
    pub offset: u64,
    pub width: u64,
}

#[derive(Debug)]
pub struct GeneratedProofs {
    pub paths: String,
    pub inputs: String,
    pub readable_fields: String,
    /// Counts include repeated guards in different edge/route lists, matching PR #80.
    pub guard_count: usize,
    pub input_guard_count: usize,
}

struct Graph {
    succ: Vec<Vec<usize>>,
    pred: Vec<Vec<usize>>,
}

impl Graph {
    fn new(cfg: &Cfg, noret: &[usize]) -> Result<Self, String> {
        let mut succ = Vec::with_capacity(cfg.flow.len());
        for (pc, flow) in cfg.flow.iter().enumerate() {
            // Mirror Lean callSucc, not Cfg::successors: syscall terminal status is
            // intentionally not used by the generic path checker.
            succ.push(match flow {
                Flow::Call(t) if noret.contains(t) => vec![],
                Flow::Exit | Flow::CallReg => vec![],
                Flow::Jump(t) => vec![*t],
                Flow::Branch(t) => vec![*t, pc + 1],
                Flow::Unresolved => return Err(format!("unresolved flow at PC {pc}")),
                _ => vec![pc + 1],
            });
        }
        let mut pred = vec![vec![]; succ.len()];
        for (pc, targets) in succ.iter().enumerate() {
            for &target in targets {
                if target >= pred.len() {
                    return Err(format!("out-of-bounds successor {pc} -> {target}"));
                }
                pred[target].push(pc);
            }
        }
        Ok(Self { succ, pred })
    }

    fn reach(&self, start: usize, stops: &[usize], backward: bool) -> Vec<bool> {
        let mut seen = vec![false; self.succ.len()];
        let mut work = vec![start];
        while let Some(pc) = work.pop() {
            if seen[pc] {
                continue;
            }
            seen[pc] = true;
            if stops.contains(&pc) {
                continue;
            }
            work.extend(if backward {
                &self.pred[pc]
            } else {
                &self.succ[pc]
            });
        }
        seen
    }

    fn guards(&self, cfg: &Cfg, start: usize, edge: usize) -> Vec<Guard> {
        let back = self.reach(edge, &[], true);
        let forward = self.reach(start, &[], false);
        (0..self.succ.len())
            .filter_map(|pc| {
                if pc == edge
                    || !back[pc]
                    || !forward[pc]
                    || !matches!(cfg.flow[pc], Flow::Branch(_))
                {
                    return None;
                }
                let on: Vec<_> = self.succ[pc].iter().copied().filter(|&q| back[q]).collect();
                (on.len() == 1 && !self.reach(start, &[pc], false)[edge])
                    .then(|| Guard { pc, on: on[0] })
            })
            .collect()
    }
}

struct Guard {
    pc: usize,
    on: usize,
}

fn jump(image: &ProgramImage, cfg: &Cfg, guard: &Guard) -> Result<(String, String), String> {
    let i = &image.insns[guard.pc];
    let Flow::Branch(target) = cfg.flow[guard.pc] else {
        return Err("guard is not conditional".into());
    };
    let op = match i.opc & 0xf0 {
        ebpf::BPF_JEQ => "jeq",
        ebpf::BPF_JNE => "jne",
        ebpf::BPF_JGT => "jgt",
        ebpf::BPF_JGE => "jge",
        ebpf::BPF_JLT => "jlt",
        ebpf::BPF_JLE => "jle",
        ebpf::BPF_JSGT => "jsgt",
        ebpf::BPF_JSGE => "jsge",
        ebpf::BPF_JSLT => "jslt",
        ebpf::BPF_JSLE => "jsle",
        ebpf::BPF_JSET => "jset",
        _ => return Err(format!("unsupported guard opcode at {}", guard.pc)),
    };
    let (src, txt) = if i.opc & ebpf::BPF_X != 0 {
        (format!("(.reg .r{})", i.src), format!("r{}", i.src))
    } else {
        let imm = if i.imm < 0 {
            format!("({})", i.imm)
        } else {
            i.imm.to_string()
        };
        (format!("(.imm {imm})"), i.imm.to_string())
    };
    Ok((
        format!(
            "{{ pc := {}, insn := .{op} .r{} {src} {target}, onSucc := {} }}",
            guard.pc, i.dst, guard.on
        ),
        format!("{op} r{}, {txt}, {target}", i.dst),
    ))
}

fn guard_list(
    image: &ProgramImage,
    cfg: &Cfg,
    name: &str,
    doc: &str,
    guards: &[Guard],
) -> Result<String, String> {
    let mut out = format!("/-- {doc} -/\ndef {name} : List Guard := [\n");
    for (index, guard) in guards.iter().enumerate() {
        let (literal, text) = jump(image, cfg, guard)?;
        let comma = if index + 1 == guards.len() { "" } else { "," };
        writeln!(out, "  {literal}{comma}  -- {text}").unwrap();
    }
    out.push(']');
    Ok(out)
}

fn input_list(
    image: &ProgramImage,
    cfg: &Cfg,
    map: &[Option<provenance::AState>],
    name: &str,
    guards: &[Guard],
) -> Result<(String, usize), String> {
    let mut items = Vec::new();
    for guard in guards {
        let Some(a) = &map[guard.pc] else {
            continue;
        };
        let i = &image.insns[guard.pc];
        let dv = &a.regs[i.dst as usize];
        let sv = if i.opc & ebpf::BPF_X != 0 {
            a.regs[i.src as usize].clone()
        } else {
            AVal::Const(i.imm as u64)
        };
        if *dv == AVal::Top || sv == AVal::Top {
            continue;
        }
        let (literal, text) = jump(image, cfg, guard)?;
        items.push((format!("  ⟨{literal}, {dv}, {sv}⟩"), text));
    }
    let mut out = format!("def i{name} : List IGuard := [\n");
    for (index, (item, text)) in items.iter().enumerate() {
        let comma = if index + 1 == items.len() { "" } else { "," };
        writeln!(out, "{item}{comma}  -- {text}").unwrap();
    }
    out.push(']');
    Ok((out, items.len()))
}

fn distinct(values: &[usize]) -> bool {
    values.iter().collect::<BTreeSet<_>>().len() == values.len()
}

/// Generate certificates only after validating all manual bindings against this artifact.
/// No filesystem writes or Lean runtime are needed. Lean remains the authority on proofs.
pub fn generate(image: &ProgramImage, input: &BaselineInputs) -> Result<GeneratedProofs, String> {
    if input.schema_version != 1 {
        return Err("unsupported success-proof schema version".into());
    }
    let actual = format!("{:x}", Sha256::digest(&image.elf_bytes));
    if input.artifact_sha256 != actual {
        return Err(format!(
            "artifact SHA-256 mismatch: expected {}, got {actual}",
            input.artifact_sha256
        ));
    }
    if image.version != SBPFVersion::V0 {
        return Err("stage-1 success emitter supports V0 only".into());
    }
    let cfg = Cfg::build(image)?;
    if input.entry != cfg.entry {
        return Err("entry does not match artifact".into());
    }
    if input.noreturn.is_empty()
        || !distinct(&input.noreturn)
        || input.noreturn.iter().any(|pc| !cfg.noreturn.contains(pc))
    {
        return Err("invalid noreturn helper bindings".into());
    }
    let graph = Graph::new(&cfg, &input.noreturn)?;
    let reachable = graph.reach(input.entry, &[], false);
    if cfg
        .flow
        .iter()
        .enumerate()
        .any(|(pc, f)| reachable[pc] && *f == Flow::CallReg)
    {
        return Err("reachable callx is unsupported".into());
    }
    for guard in &input.guard_pins {
        let Some(Flow::Branch(target)) = cfg.flow.get(guard.pc) else {
            return Err("invalid guard PC".into());
        };
        if (guard.on_success != *target && guard.on_success != guard.pc + 1)
            || guard.edge >= image.insns.len()
            || !graph
                .guards(&cfg, input.entry, guard.edge)
                .iter()
                .any(|g| g.pc == guard.pc && g.on == guard.on_success)
        {
            return Err(format!("invalid guard successor at {}", guard.pc));
        }
    }
    let success = cfg.outcomes(image).success_edges();
    let edge_pcs: Vec<_> = input.edges.iter().map(|e| e.pc).collect();
    if edge_pcs.is_empty() || !distinct(&edge_pcs) {
        return Err("empty or duplicate success edges".into());
    }
    let mut names = BTreeSet::new();
    for field in &input.readable_fields {
        let name = format!("field_{}", field.name.replace('.', "_"));
        let identifier = field.name.split('.').all(|part| {
            !part.is_empty()
                && part
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
        });
        if !identifier
            || !names.insert(name.clone())
            || !names.insert(format!("{name}_width"))
            || field.width == 0
            || field.offset.checked_add(field.width).is_none()
        {
            return Err("invalid readable field mapping".into());
        }
    }
    for edge in &input.edges {
        if !success.contains(&edge.pc) {
            return Err(format!("PC {} is not an artifact success edge", edge.pc));
        }
        if edge.checkpoints.is_empty() || !distinct(&edge.checkpoints) {
            return Err("empty or duplicate checkpoints".into());
        }
        for &pc in &edge.checkpoints {
            if pc >= image.insns.len() || !reachable[pc] || !graph.reach(pc, &[], false)[edge.pc] {
                return Err(format!("invalid checkpoint {pc} for edge {}", edge.pc));
            }
        }
        if graph.reach(input.entry, &edge.checkpoints, false)[edge.pc] {
            return Err(format!("checkpoints do not cut edge {}", edge.pc));
        }
        // Descriptions are Lean comments, never source-code escape hatches.
        for desc in [&edge.description, &edge.input_description] {
            if desc.contains("-/") || desc.contains("/-") || desc.contains(['\n', '\r']) {
                return Err("invalid edge description".into());
            }
        }
    }
    let map = abstract_map(image, &cfg, &graph.succ, input.entry)?;
    let noret = input
        .noreturn
        .iter()
        .map(|pc| format!("t == {pc}"))
        .collect::<Vec<_>>()
        .join(" || ");
    let mut paths = include_str!("success_proofs/paths_head.lean.in")
        .replace("t == 11177 || t == 10881", &noret);
    let mut inputs =
        include_str!("success_proofs/inputs_head.lean.in").replace("198", &input.entry.to_string());
    // The original modules leave a blank line between the header and edge blocks.
    paths.push('\n');
    inputs.push('\n');
    let mut guard_count = 0;
    let mut input_guard_count = 0;
    let mut path_blocks = Vec::new();
    let mut input_blocks = Vec::new();
    for edge in &input.edges {
        let e = edge.pc;
        path_blocks.push(format!("/-! ### Edge {e}: {} -/\n", edge.description));
        input_blocks.push(format!("/-! ### Edge {e}: {} -/", edge.input_description));
        let mut lists = vec![(
            format!("dom{e}"),
            format!("Guards every run from the entrypoint to {e} passes."),
            graph.guards(&cfg, input.entry, e),
        )];
        for &c in &edge.checkpoints {
            lists.push((
                format!("pre{e}_{c}"),
                format!("Guards from the entrypoint to checkpoint {c}."),
                graph.guards(&cfg, input.entry, c),
            ));
            lists.push((
                format!("post{e}_{c}"),
                format!("Guards from checkpoint {c} on to {e}."),
                graph.guards(&cfg, c, e),
            ));
        }
        for (name, doc, guards) in lists {
            guard_count += guards.len();
            path_blocks.push(guard_list(image, &cfg, &name, &doc, &guards)?);
            let (source, count) = input_list(image, &cfg, &map, &name, &guards)?;
            input_guard_count += count;
            input_blocks.push(source);
        }
        let routes = edge
            .checkpoints
            .iter()
            .map(|c| format!("({c}, pre{e}_{c}, post{e}_{c})"))
            .collect::<Vec<_>>()
            .join(", ");
        path_blocks.push(format!(
            "/-- Edge {e}'s authority routes. -/\ndef routes{e} : List Route :=\n  [{routes}]"
        ));
        path_blocks.push(
            include_str!("success_proofs/path_theorem.lean.in")
                .replace("@EDGE@", &e.to_string())
                .replace("@DESC@", &edge.description)
                .replace("198", &input.entry.to_string()),
        );
        let iroutes = edge
            .checkpoints
            .iter()
            .map(|c| format!("({c}, ipre{e}_{c}, ipost{e}_{c})"))
            .collect::<Vec<_>>()
            .join(", ");
        input_blocks.push(format!("def iroutes{e} : List IRoute :=\n  [{iroutes}]"));
        // Original generator separated pins and inputs by a blank line.
        input_blocks.push(
            include_str!("success_proofs/input_theorem.lean.in")
                .replace("@EDGE@", &e.to_string())
                .replace("@DESC@", &edge.input_description)
                .replace("198", &input.entry.to_string()),
        );
    }
    paths.push_str(&path_blocks.join("\n\n"));
    paths.push_str("\n\n\nend Examples.PTokenSuccessPaths\n");
    inputs.push_str(&input_blocks.join("\n\n"));
    inputs.push_str("\n\nend Examples.PTokenSuccessPaths\n");
    let mut readable_fields = String::from("/- Generated from success-proof-inputs.json; untrusted readable bindings, not assumptions. -/\nnamespace Examples.PTokenReadableFields\n\n");
    for field in &input.readable_fields {
        let name = format!("field_{}", field.name.replace('.', "_"));
        writeln!(
            readable_fields,
            "abbrev {name} : Nat := {}\nabbrev {name}_width : Nat := {}\n",
            field.offset, field.width
        )
        .unwrap();
    }
    readable_fields.push_str("end Examples.PTokenReadableFields\n");
    Ok(GeneratedProofs {
        paths,
        inputs,
        readable_fields,
        guard_count,
        input_guard_count,
    })
}
