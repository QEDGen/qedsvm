//! Success proofs from discovered bindings (solana-skills#450). Emits a text module and a
//! success module for any program: guard and pin lists (shared with the p_token emitter),
//! the generic no-return check, the assumed-length abstract map, and one readable
//! theorem per edge. Every generated fact is re-checked by Lean.

use super::{guard_list, input_list, provenance::abstract_map_with, AVal, Graph, Guard};
use crate::{
    cfg::Cfg, discover::bindings::Bindings, image::ProgramImage,
    input_layout::aligned_input_offsets,
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use solana_sbpf::{ebpf, program::SBPFVersion};
use std::collections::BTreeMap;
use std::fmt::Write;

/// Lean names for one program's modules.
pub struct ProgramNames {
    /// Module directory and namespace suffix, e.g. `LabelVault`.
    pub prefix: String,
}

/// A guard on a route whose operands the map does not pin: Lean proves nothing about it.
#[derive(Debug, Default, Serialize, PartialEq, Eq)]
pub struct UnpinnedGuard {
    pub pc: usize,
    pub insn: String,
}

/// What one route's readable theorem states, read off the pinned facts it emits.
#[derive(Debug, Default, Serialize, PartialEq, Eq)]
pub struct RouteFacts {
    pub edge: usize,
    pub route: usize,
    pub discriminator: u64,
    /// Accounts whose `is_signer` byte the conclusion states is nonzero.
    pub proven_signers: Vec<usize>,
    /// Key compares whose four limb equalities the conclusion states.
    pub proven_key_compares: Vec<String>,
    pub unpinned: Vec<UnpinnedGuard>,
    /// Local calls between the route and the edge; guards inside them are not seen.
    pub opaque_calls: Vec<usize>,
}

/// One assumed account data length: a hypothesis of the edge's theorem.
#[derive(Debug, Default, Serialize, PartialEq, Eq)]
pub struct AssumedLength {
    pub edge: usize,
    pub account: usize,
    pub value: u64,
    /// Discovery's claim that the program also checks it on every path.
    pub checked: bool,
}

#[derive(Debug, Default, Serialize, PartialEq, Eq)]
pub struct Coverage {
    pub instructions: usize,
    pub success_edges: usize,
    pub proven_edges: usize,
    pub routes: usize,
    pub guards: usize,
    pub pinned_guards: usize,
    pub readable_facts: usize,
    pub field_labels: usize,
    pub refused_labels: usize,
    pub unchecked_lengths: usize,
    pub unsupported_edges: usize,
    pub native_decide_uses: usize,
    pub route_facts: Vec<RouteFacts>,
    pub assumed_lengths: Vec<AssumedLength>,
}

pub struct GeneratedModules {
    pub text: String,
    pub success: String,
    pub coverage: Coverage,
}

struct Pinned {
    op: &'static str,
    dv: AVal,
    sv: AVal,
    taken: bool,
}

/// The pinned guards in the order `input_list` emits them (same filter).
fn pinned(
    image: &ProgramImage,
    cfg: &Cfg,
    map: &[Option<super::provenance::AState>],
    guards: &[Guard],
) -> Result<(Vec<Pinned>, Vec<UnpinnedGuard>), String> {
    let mut out = Vec::new();
    let mut skipped = Vec::new();
    for g in guards {
        let unpinned = || -> Result<UnpinnedGuard, String> {
            Ok(UnpinnedGuard {
                pc: g.pc,
                insn: super::jump(image, cfg, g)?.1,
            })
        };
        let Some(a) = &map[g.pc] else {
            skipped.push(unpinned()?);
            continue;
        };
        let i = &image.insns[g.pc];
        let dv = a.regs[i.dst as usize].clone();
        let sv = if i.opc & ebpf::BPF_X != 0 {
            a.regs[i.src as usize].clone()
        } else {
            AVal::Const(i.imm as u64)
        };
        if dv == AVal::Top || sv == AVal::Top {
            skipped.push(unpinned()?);
            continue;
        }
        let crate::cfg::Flow::Branch(target) = cfg.flow[g.pc] else {
            continue;
        };
        let op = match i.opc & 0xf0 {
            ebpf::BPF_JEQ => "=",
            ebpf::BPF_JNE => "≠",
            ebpf::BPF_JGT => ">",
            ebpf::BPF_JGE => "≥",
            ebpf::BPF_JLT => "<",
            ebpf::BPF_JLE => "≤",
            ebpf::BPF_JSGT => "s>",
            ebpf::BPF_JSGE => "s≥",
            ebpf::BPF_JSLT => "s<",
            ebpf::BPF_JSLE => "s≤",
            _ => "&",
        };
        out.push(Pinned {
            op,
            dv,
            sv,
            taken: g.on == target,
        });
    }
    Ok((out, skipped))
}

/// Whether the fact states equality (`=` taken, or `≠` not taken).
fn states_eq(p: &Pinned) -> bool {
    (p.op == "=" && p.taken) || (p.op == "≠" && !p.taken)
}

/// Whether the fact states inequality (`≠` taken, or `=` not taken).
fn states_ne(p: &Pinned) -> bool {
    (p.op == "≠" && p.taken) || (p.op == "=" && !p.taken)
}

/// Signers and key compares that the pinned facts state, with the right polarity.
fn proven_authority(facts: &[&Pinned], regions: &[(u64, u64, u64)]) -> (Vec<usize>, Vec<String>) {
    let mut signers = std::collections::BTreeSet::new();
    let mut limbs: BTreeMap<(usize, u64), std::collections::BTreeSet<u64>> = BTreeMap::new();
    for p in facts {
        for (n, &(h, _, _)) in regions.iter().enumerate() {
            if p.dv == AVal::InLoad("byte", h + 1) && p.sv == AVal::Const(0) && states_ne(p) {
                signers.insert(n);
            }
        }
        if !states_eq(p) {
            continue;
        }
        if let (AVal::InLoad("dword", x), AVal::InLoad("dword", y)) = (&p.dv, &p.sv) {
            for (a, b) in [(*x, *y), (*y, *x)] {
                for (n, &(h, _, _)) in regions.iter().enumerate() {
                    let key = h + 8;
                    if (key..key + 32).contains(&a) && (a - key) % 8 == 0 {
                        if let Some(base) = b.checked_sub(a - key) {
                            limbs.entry((n, base)).or_default().insert(a - key);
                        }
                    }
                }
            }
        }
    }
    let mut keys = Vec::new();
    for ((acct, base), ks) in limbs {
        if ks.len() != 4 {
            continue;
        }
        for (b, &(_, d, l)) in regions.iter().enumerate() {
            if base >= d && base + 32 <= d + l {
                keys.push(format!(
                    "account {acct} key == account {b} data[{}..{}]",
                    base - d,
                    base - d + 32
                ));
            }
        }
    }
    keys.sort();
    (signers.into_iter().collect(), keys)
}

/// Text that is safe inside a Lean doc comment.
fn doc_safe(text: &str) -> String {
    text.replace("-/", "- /").replace("/-", "/ -")
}

fn sanitize(name: &str) -> Option<String> {
    let s: String = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_ascii_lowercase()
            } else {
                '_'
            }
        })
        .collect();
    (!s.is_empty() && s.chars().next().unwrap().is_ascii_alphabetic()).then_some(s)
}

/// Readable names for input words, from the Solana input layout and field labels.
struct Names {
    regions: Vec<(u64, u64, u64)>,
    instruction_data: u64,
    fields: BTreeMap<(usize, u64), String>,
    used: BTreeMap<String, (u64, &'static str)>,
    defs: BTreeMap<(u64, &'static str), String>,
}

impl Names {
    fn base(&self, off: u64) -> String {
        if off == 0 {
            return "num_accounts".into();
        }
        for (n, &(h, d, l)) in self.regions.iter().enumerate() {
            let limb = |start: u64| format!("{}", (off - start) / 8);
            match off {
                o if o == h => return format!("acct{n}_dup_marker"),
                o if o == h + 1 => return format!("acct{n}_is_signer"),
                o if o == h + 2 => return format!("acct{n}_is_writable"),
                o if o == h + 3 => return format!("acct{n}_executable"),
                o if (h + 8..h + 40).contains(&o) => return format!("acct{n}_key_{}", limb(h + 8)),
                o if (h + 40..h + 72).contains(&o) => {
                    return format!("acct{n}_owner_{}", limb(h + 40))
                }
                o if o == h + 72 => return format!("acct{n}_lamports"),
                o if o == h + 80 => return format!("acct{n}_data_len"),
                o if (d..d + l).contains(&o) => {
                    let rel = o - d;
                    return match self.fields.get(&(n, rel)) {
                        Some(f) => format!("acct{n}_{f}_{rel}"),
                        None => format!("acct{n}_data_{rel}"),
                    };
                }
                _ => {}
            }
        }
        if off + 8 == self.instruction_data {
            return "ix_data_len".into();
        }
        if off >= self.instruction_data {
            return format!("ix_data_{}", off - self.instruction_data);
        }
        format!("input_{off}")
    }

    fn name(&mut self, off: u64, w: &'static str) -> String {
        if let Some(n) = self.defs.get(&(off, w)) {
            return n.clone();
        }
        let mut n = self.base(off);
        if self.used.get(&n).is_some_and(|k| *k != (off, w)) {
            n = format!("{n}_{w}");
        }
        self.used.insert(n.clone(), (off, w));
        self.defs.insert((off, w), n.clone());
        n
    }

    fn term(&mut self, v: &AVal) -> String {
        match v {
            AVal::Const(c) => c.to_string(),
            AVal::InLoad(w, off) => format!("{} s0", self.name(*off, w)),
            AVal::InPtr(o) => format!("(INPUT_START + {o})"),
            AVal::Fp => "STACK_TOP".into(),
            AVal::Top => "0".into(),
        }
    }

    fn fact(&mut self, p: &Pinned) -> String {
        let (a, b) = (self.term(&p.dv), self.term(&p.sv));
        let cond = match p.op {
            "s>" => format!("toSigned64 ({a}) > toSigned64 ({b})"),
            "s≥" => format!("toSigned64 ({a}) ≥ toSigned64 ({b})"),
            "s<" => format!("toSigned64 ({a}) < toSigned64 ({b})"),
            "s≤" => format!("toSigned64 ({a}) ≤ toSigned64 ({b})"),
            "&" => format!("{a} &&& {b} ≠ 0"),
            op => format!("{a} {op} {b}"),
        };
        match (p.taken, p.op) {
            (true, _) => cond,
            (false, "=") => format!("{a} ≠ {b}"),
            (false, "≠") => format!("{a} = {b}"),
            (false, _) => format!("¬ ({cond})"),
        }
    }
}

fn text_module(image: &ProgramImage, prefix: &str, sha: &str) -> String {
    let mut reg: Vec<(u32, usize)> = image
        .executable
        .get_function_registry()
        .iter()
        .map(|(k, (_n, slot))| (k, slot))
        .collect();
    reg.sort_by_key(|(k, _)| *k);
    let reg = reg
        .iter()
        .map(|(k, s)| format!("({k}, {s})"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut out = format!(
        "/- GENERATED by `qed-success-proofs --bindings` from the ELF with SHA-256\n   {sha}. Regenerate; do not edit. -/\nimport SVM.SBPF.Decode\n\nnamespace Examples.{prefix}\n\nopen SVM.SBPF\n\n/-- The `.text` bytes, {} bytes. -/\ndef text : ByteArray := Decode.bytesOfHex \"\n",
        image.text_bytes.len()
    );
    for chunk in image.text_bytes.chunks(64) {
        let line: String = chunk.iter().map(|b| format!("{b:02x}")).collect();
        writeln!(out, "  {line}").unwrap();
    }
    write!(
        out,
        "  \"\n\n/-- The V0 function registry (murmur3 key, target slot), as solana-sbpf builds it. -/\ndef fnRegistry : List (Nat × Nat) := [{reg}]\n\nend Examples.{prefix}\n"
    )
    .unwrap();
    out
}

fn conj(facts: &[String]) -> String {
    if facts.is_empty() {
        "True".into()
    } else {
        facts.join(" ∧\n    ")
    }
}

/// The proof that `h`'s guards give each fact, one bullet per fact.
fn facts_proof(lists: &[(&str, &str, usize)], simp: &str) -> String {
    let total: usize = lists.iter().map(|l| l.2).sum();
    if total == 0 {
        return "trivial".into();
    }
    let mut out = String::new();
    if total > 1 {
        write!(out, "refine ⟨{}⟩", vec!["?_"; total].join(", ")).unwrap();
    }
    for (hyp, list, count) in lists {
        for k in 0..*count {
            write!(
                out,
                "\n  · have h := {hyp} ({list}[{k}]'(by decide)) (List.getElem_mem _)\n    simpa [{simp}] using h"
            )
            .unwrap();
        }
    }
    out.trim_start_matches('\n').trim_start().to_string()
}

pub fn generate_from_bindings(
    image: &ProgramImage,
    b: &Bindings,
    names: &ProgramNames,
) -> Result<GeneratedModules, String> {
    let sha = format!("{:x}", Sha256::digest(&image.elf_bytes));
    if b.schema_version != 1 || b.artifact_sha256 != sha {
        return Err(format!(
            "bindings are for {}, not this artifact ({sha})",
            b.artifact_sha256
        ));
    }
    if image.version != SBPFVersion::V0 {
        return Err("the success emitter supports V0 only".into());
    }
    if sanitize(&names.prefix).is_none() || !names.prefix.chars().all(|c| c.is_ascii_alphanumeric())
    {
        return Err("invalid module prefix".into());
    }
    let cfg = Cfg::build(image)?;
    if b.entry != cfg.entry {
        return Err("entry does not match artifact".into());
    }
    let heads = &b.noreturn.heads;
    if heads.iter().any(|h| !cfg.noreturn.contains(h)) {
        return Err("a no-return head is not a no-return function of this artifact".into());
    }
    let graph = Graph::new(&cfg, heads)?;
    let success = cfg.outcomes(image).success_edges();
    let p = &names.prefix;
    let entry = b.entry;
    let mut cov = Coverage {
        instructions: b.instructions.len(),
        success_edges: success.len(),
        unsupported_edges: b.unsupported.len(),
        native_decide_uses: 2,
        ..Coverage::default()
    };
    let noret = if heads.is_empty() {
        "false".to_string()
    } else {
        heads
            .iter()
            .map(|h| format!("t == {h}"))
            .collect::<Vec<_>>()
            .join(" || ")
    };
    let mut out = format!(
        "/-
  Success-path theorems for `{p}` (GENERATED by `qed-success-proofs --bindings`;
  regenerate, do not edit). Every binding comes from `qed-discover` and is untrusted: the
  `native_decide` checks below re-check each guard, route cut, no-return chain and input pin
  against the decoded program. Names are labels from the Solana input layout and DWARF; no
  proof depends on them. Each edge's theorem assumes the account data lengths it states.
-/
import {p}.Text
import SVM.SBPF.NoReturnCheck
import SVM.SBPF.InputGuards
import SVM.SBPF.Runner

namespace Examples.{p}

open SVM.SBPF Memory

/-- The decoded `.text`, as the runner loads it. -/
@[irreducible] def insns? : Option (Array Insn) := Decode.decodeProgramV0 text fnRegistry

/-- The text decodes. Without this, every `insns?.all` check below would hold vacuously. -/
theorem decodes : insns?.isSome = true := by
  native_decide

/-- The decoded program. -/
def prog : Array Insn := insns?.get decodes

theorem insns?_eq : insns? = some prog := (Option.some_get decodes).symm

/-- No-return witness from `qed-discover`. -/
def noRetWitness : NoRetWitness :=
  {}

theorem noRetWitness_ok : insns?.all (fun insns =>
    noRetCheck (Runner.fetchFromArray insns) noRetWitness) = true := by
  native_decide

/-- Calls that never return. -/
def noret (t : Nat) : Bool := {noret}

theorem noret_sound (insns : Array Insn) (hp : insns? = some insns) :
    ∀ t, noret t = true → NoReturn (Runner.fetchFromArray insns) t := by
  have h := noRetWitness_ok
  rw [hp, Option.all_some] at h
  intro t ht
  apply noRetCheck_sound _ _ h
  simp only [noret, Bool.or_eq_true, beq_iff_eq] at ht
  simp only [noRetWitness, List.mem_cons, List.mem_nil_iff, or_false]
  omega

/-- The entrypoint's initial abstract state: `r1` points at the input, `r10` is the frame
    pointer, no input has been written. -/
def init : AState := {{ r1 := .inPtr 0, r10 := .fp, written := some [] }}

theorem init_concrete (s0 : State) (h1 : s0.regs.r1 = INPUT_START)
    (h10 : s0.regs.r10 = STACK_TOP) : Concrete s0 init s0 := by
  refine ⟨fun r => ?_, fun _ _ _ _ _ => rfl⟩
  cases r
  case r1 => show s0.regs.r1 = INPUT_START + 0; rw [h1]; rfl
  case r10 => exact h10
  all_goals trivial
",
        b.noreturn.to_lean()
    );
    let ix_name: BTreeMap<u64, Option<String>> = b
        .instructions
        .iter()
        .map(|i| (i.discriminator, i.handler.clone()))
        .collect();
    for e in &b.edges {
        if !success.contains(&e.pc) {
            return Err(format!("{} is not a success edge of this artifact", e.pc));
        }
        if e.routes.is_empty() {
            return Err(format!("edge {} has no routes", e.pc));
        }
        let ep = e.pc;
        let lengths: Vec<usize> = e.assumed.iter().map(|w| w.value as usize).collect();
        let offsets = aligned_input_offsets(&lengths).map_err(str::to_string)?;
        let regions: Vec<(u64, u64, u64)> = offsets
            .account_data
            .iter()
            .zip(&lengths)
            .map(|(&d, &l)| (d as u64 - 88, d as u64, l as u64))
            .collect();
        let mut nm = Names {
            regions,
            instruction_data: e.instruction_data,
            fields: e
                .fields
                .iter()
                .filter_map(|f| Some(((f.account, f.data_offset), sanitize(f.name.as_ref()?)?)))
                .collect(),
            used: BTreeMap::new(),
            defs: BTreeMap::new(),
        };
        cov.field_labels += e.fields.iter().filter(|f| f.name.is_some()).count();
        cov.refused_labels += e.fields.iter().filter(|f| f.name.is_none()).count();
        cov.unchecked_lengths += e.assumed.iter().filter(|w| !w.checked).count();
        let asm: Vec<(u64, super::provenance::Width, u64)> = e
            .assumed
            .iter()
            .map(|w| (w.offset, super::provenance::Width::Dword, w.value))
            .collect();
        let map = abstract_map_with(image, &cfg, &graph.succ, entry, &asm)?;
        let mut blocks = vec![format!("/-! ## Edge {ep} -/")];
        let dom = graph.guards(&cfg, entry, ep);
        let mut lists = vec![(
            format!("dom{ep}"),
            format!("Guards every run from the entrypoint to {ep} passes."),
            dom,
        )];
        for r in &e.routes {
            let c = r.pc;
            lists.push((
                format!("pre{ep}_{c}"),
                format!("Guards from the entrypoint to route {c}."),
                graph.guards(&cfg, entry, c),
            ));
            lists.push((
                format!("post{ep}_{c}"),
                format!("Guards from route {c} on to {ep}."),
                graph.guards(&cfg, c, ep),
            ));
        }
        let mut ilists = Vec::new();
        let mut pins = BTreeMap::new();
        for (name, doc, guards) in &lists {
            cov.guards += guards.len();
            blocks.push(guard_list(image, &cfg, name, doc, guards)?);
            let (src, count) = input_list(image, &cfg, &map, name, guards)?;
            cov.pinned_guards += count;
            ilists.push(src);
            pins.insert(name.clone(), pinned(image, &cfg, &map, guards)?);
        }
        let routes = e
            .routes
            .iter()
            .map(|r| format!("({0}, pre{ep}_{0}, post{ep}_{0})", r.pc))
            .collect::<Vec<_>>()
            .join(", ");
        let iroutes = e
            .routes
            .iter()
            .map(|r| format!("({0}, ipre{ep}_{0}, ipost{ep}_{0})", r.pc))
            .collect::<Vec<_>>()
            .join(", ");
        blocks.push(format!("/-- Edge {ep}'s routes: one per dispatch arm. -/\ndef routes{ep} : List Route :=\n  [{routes}]"));
        blocks.push(format!(
            "theorem check{ep} : insns?.all (fun insns =>\n    edgeCheck (Runner.fetchFromArray insns) noret insns.size {entry} {ep} dom{ep} routes{ep}) = true := by\n  native_decide"
        ));
        let asm_lean = e
            .assumed
            .iter()
            .map(|w| format!("({}, .dword, {})", w.offset, w.value))
            .collect::<Vec<_>>()
            .join(", ");
        blocks.push(format!(
            "/-- The account data lengths edge {ep}'s map assumes. -/\ndef assumed{ep} : Assumed := [{asm_lean}]\n\ndef absMap{ep} (insns : Array Insn) : Array (Option AState) :=\n  absMapWith (absStepA assumed{ep}) (Runner.fetchFromArray insns) noret insns.size {entry} init\n\ntheorem absOk{ep} : insns?.all (fun insns =>\n    absCheckWith (absStepA assumed{ep}) (Runner.fetchFromArray insns) noret (absMap{ep} insns)\n      {entry} init) = true := by\n  native_decide"
        ));
        blocks.extend(ilists);
        blocks.push(format!("def iroutes{ep} : List IRoute :=\n  [{iroutes}]"));
        blocks.push(format!(
            "theorem pins{ep} : insns?.all (fun insns =>\n    let m := absMap{ep} insns\n    (idom{ep}.all (iguardCheck m) &&\n      iroutes{ep}.all fun (_, ip, iq) => ip.all (iguardCheck m) && iq.all (iguardCheck m)) &&\n    iguardsMatch dom{ep} routes{ep} idom{ep} iroutes{ep}) = true := by native_decide"
        ));
        blocks.push(format!(
            "/-- **Input conditions for edge {ep}.** A run from the entrypoint that stands at the edge
    started from an input that passed the pinned dominating guards and one route's pinned
    guards, given the assumed lengths. -/
theorem inputs{ep} (insns : Array Insn) (hp : insns? = some insns) (s0 : State)
    (hasm : AssumedHolds s0 assumed{ep}) (hpc : s0.pc = {entry}) (hcs : s0.callStack = [])
    (hinit : Concrete s0 init s0) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = {ep}) :
    (∀ ig ∈ idom{ep}, ig.holds s0) ∧
    ∃ c ip iq, (c, ip, iq) ∈ iroutes{ep} ∧ (∀ ig ∈ ip, ig.holds s0) ∧ (∀ ig ∈ iq, ig.holds s0) := by
  have hpath := check{ep}
  rw [hp, Option.all_some] at hpath
  have habs := absOk{ep}
  rw [hp, Option.all_some] at habs
  have hpins := pins{ep}
  rw [hp, Option.all_some] at hpins
  simp only [Bool.and_eq_true] at hpins
  exact edge_input_conditionsA _ noret (noret_sound insns hp) _ {entry} {ep} _ _ _ _ assumed{ep} _ _
    hpath habs (by simpa only [Bool.and_eq_true] using hpins.1) hpins.2 s0 hasm hpc hcs hinit n hend"
        ));
        cov.native_decide_uses += 3;
        // Readable layer.
        let dom_facts: Vec<String> = pins[&format!("dom{ep}")]
            .0
            .iter()
            .map(|x| nm.fact(x))
            .collect();
        let mut route_defs = Vec::new();
        for r in &e.routes {
            let c = r.pc;
            let (dom_p, dom_skip) = &pins[&format!("dom{ep}")];
            let (pre_p, pre_skip) = &pins[&format!("pre{ep}_{c}")];
            let (post_p, post_skip) = &pins[&format!("post{ep}_{c}")];
            let pre: Vec<String> = pre_p.iter().map(|x| nm.fact(x)).collect();
            let post: Vec<String> = post_p.iter().map(|x| nm.fact(x)).collect();
            let stated: Vec<&Pinned> = dom_p.iter().chain(pre_p).chain(post_p).collect();
            let (proven_signers, proven_key_compares) = proven_authority(&stated, &nm.regions);
            let mut unpinned: Vec<UnpinnedGuard> = Vec::new();
            for u in dom_skip.iter().chain(pre_skip).chain(post_skip) {
                if !unpinned.iter().any(|x| x.pc == u.pc) {
                    unpinned.push(UnpinnedGuard {
                        pc: u.pc,
                        insn: u.insn.clone(),
                    });
                }
            }
            unpinned.sort_by_key(|u| u.pc);
            let to_edge = graph.reach(c, &[], false);
            let back = graph.reach(ep, &[], true);
            let opaque_calls: Vec<usize> = (0..cfg.flow.len())
                .filter(|&q| to_edge[q] && back[q])
                .filter(
                    |&q| matches!(cfg.flow[q], crate::cfg::Flow::Call(t) if !heads.contains(&t)),
                )
                .collect();
            cov.route_facts.push(RouteFacts {
                edge: ep,
                route: c,
                discriminator: r.discriminator,
                proven_signers,
                proven_key_compares,
                unpinned,
                opaque_calls,
            });
            route_defs.push((r, pre, post));
        }
        let len_names: Vec<String> = (0..e.assumed.len())
            .map(|n| format!("acct{n}_data_len"))
            .collect();
        for (n, w) in e.assumed.iter().enumerate() {
            nm.name(w.offset, "dword");
            debug_assert_eq!(nm.defs[&(w.offset, "dword")], len_names[n]);
        }
        let mut defs = String::new();
        for ((off, w), name) in &nm.defs {
            writeln!(
                defs,
                "def {name} (s0 : State) : Nat := readByWidth s0.mem (INPUT_START + {off}) .{w}"
            )
            .unwrap();
        }
        let def_names: Vec<&String> = nm.defs.values().collect();
        let simp = format!(
            "IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val, {}",
            def_names
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        let len_doc = e
            .assumed
            .iter()
            .enumerate()
            .map(|(n, w)| {
                if w.checked {
                    format!("account {n} has {} data bytes (the program also checks this on every path)", w.value)
                } else {
                    format!("account {n} has {} data bytes (an assumption: the program does not check it)", w.value)
                }
            })
            .collect::<Vec<_>>()
            .join("; ");
        for (n, w) in e.assumed.iter().enumerate() {
            cov.assumed_lengths.push(AssumedLength {
                edge: ep,
                account: n,
                value: w.value,
                checked: w.checked,
            });
        }
        let len_facts: Vec<String> = e
            .assumed
            .iter()
            .enumerate()
            .map(|(n, w)| format!("acct{n}_data_len s0 = {}", w.value))
            .collect();
        cov.readable_facts += dom_facts.len()
            + route_defs
                .iter()
                .map(|(_, a, b)| a.len() + b.len())
                .sum::<usize>();
        blocks.push(format!(
            "/-! ### Readable requirements for edge {ep} -/\n\n{}",
            defs.trim_end()
        ));
        blocks.push(format!(
            "/-- The input lengths edge {ep}'s theorem assumes: {len_doc}. The theorem says nothing\n    about inputs with other lengths. -/\ndef lengths{ep} (s0 : State) : Prop :=\n  {}\n\ntheorem assumed_of_lengths{ep} (s0 : State) (h : lengths{ep} s0) : AssumedHolds s0 assumed{ep} := by\n  intro x hx\n  simp only [assumed{ep}, List.mem_cons, List.mem_nil_iff, or_false] at hx\n  rcases hx with {} <;> simp_all [lengths{ep}, {}]",
            conj(&len_facts),
            vec!["rfl"; e.assumed.len().max(1)].join(" | "),
            len_names.join(", ")
        ));
        blocks.push(format!(
            "/-- What every run to edge {ep} checks, whatever the instruction. -/\ndef requires{ep} (s0 : State) : Prop :=\n  {}\n\ntheorem requires{ep}_of (s0 : State) (h : ∀ ig ∈ idom{ep}, ig.holds s0) : requires{ep} s0 := by\n  {}",
            conj(&dom_facts),
            facts_proof(&[("h", &format!("idom{ep}"), dom_facts.len())], &format!("idom{ep}, {simp}"))
        ));
        let mut disj = Vec::new();
        let mut cases = Vec::new();
        for (i, (r, pre, post)) in route_defs.iter().enumerate() {
            let c = r.pc;
            let label = ix_name
                .get(&r.discriminator)
                .cloned()
                .flatten()
                .unwrap_or_else(|| "no handler label".into());
            let facts = cov
                .route_facts
                .iter()
                .find(|f| f.edge == ep && f.route == c)
                .unwrap();
            let mut doc = format!(
                "Instruction {} (`{}`, a DWARF label), route {c}.",
                r.discriminator,
                doc_safe(&label)
            );
            for s in &facts.proven_signers {
                write!(doc, " States that account {s} signed.").unwrap();
            }
            for k in &facts.proven_key_compares {
                write!(doc, " States {k}.").unwrap();
            }
            for u in &facts.unpinned {
                write!(
                    doc,
                    " Not stated (operands not pinned): `{}` at {}.",
                    doc_safe(&u.insn),
                    u.pc
                )
                .unwrap();
            }
            for q in &facts.opaque_calls {
                write!(doc, " Calls a function at {q} whose guards are not seen.").unwrap();
            }
            let all: Vec<String> = pre.iter().chain(post).cloned().collect();
            blocks.push(format!(
                "/-- {doc} -/\ndef requires{ep}_ix{d} (s0 : State) : Prop :=\n  {}\n\ntheorem requires{ep}_ix{d}_of (s0 : State) (hp : ∀ ig ∈ ipre{ep}_{c}, ig.holds s0)\n    (hq : ∀ ig ∈ ipost{ep}_{c}, ig.holds s0) : requires{ep}_ix{d} s0 := by\n  {}",
                conj(&all),
                facts_proof(
                    &[("hp", &format!("ipre{ep}_{c}"), pre.len()), ("hq", &format!("ipost{ep}_{c}"), post.len())],
                    &format!("ipre{ep}_{c}, ipost{ep}_{c}, {simp}")
                ),
                d = r.discriminator,
            ));
            disj.push(format!("requires{ep}_ix{} s0", r.discriminator));
            let n = route_defs.len();
            let mut inj = format!("requires{ep}_ix{}_of s0 hip hiq", r.discriminator);
            if i + 1 < n {
                inj = format!("Or.inl ({inj})");
            }
            for _ in 0..i {
                inj = format!("Or.inr ({inj})");
            }
            cases.push(format!("  · exact {inj}"));
        }
        cov.routes += e.routes.len();
        let pats = vec!["⟨rfl, rfl, rfl⟩"; e.routes.len()].join(" | ");
        blocks.push(format!(
            "/-- **Readable requirements for edge {ep}.** A run from the entrypoint that stands at the
    edge started from an input with the stated lengths that meets the edge's checks and one
    instruction's checks. -/
theorem readable{ep} (s0 : State)
    (hlen : lengths{ep} s0) (hpc : s0.pc = {entry}) (hcs : s0.callStack = [])
    (h1 : s0.regs.r1 = INPUT_START) (h10 : s0.regs.r10 = STACK_TOP) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray prog) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray prog) s0 n).pc = {ep}) :
    requires{ep} s0 ∧ ({}) := by
  obtain ⟨hdom, c, ip, iq, hr, hip, hiq⟩ :=
    inputs{ep} prog insns?_eq s0 (assumed_of_lengths{ep} s0 hlen) hpc hcs (init_concrete s0 h1 h10) n hend
  refine ⟨requires{ep}_of s0 hdom, ?_⟩
  simp only [iroutes{ep}, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hr
  rcases hr with {pats}
{}",
            disj.join(" ∨ "),
            cases.join("\n")
        ));
        cov.proven_edges += 1;
        out.push('\n');
        out.push_str(&blocks.join("\n\n"));
        out.push('\n');
    }
    write!(out, "\nend Examples.{p}\n").unwrap();
    Ok(GeneratedModules {
        text: text_module(image, p, &sha),
        success: out,
        coverage: cov,
    })
}
