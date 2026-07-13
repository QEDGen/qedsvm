//! One-arm lift orchestration: prelude emission, theorem-binder assembly
//! (`TripleCtx`) and the corollary emitters (heap-alloc / balance /
//! typed-fault / transition) around `lift_one_with_layouts`.

use std::path::Path;

use solana_sbpf::{ebpf, static_analysis::Analysis};

use crate::core::{Atom, Expr, Width};
use crate::diagnostic::{DiagnosticKind, LiftError};
use crate::emit::{
    atoms_to_lean, atoms_to_lean_heap, build_sat_witness, fold_abstractions, heap_cell_addr,
    post_atoms, region_req,
};
use crate::exec::{imm_is_modeled_syscall, walk_and_exec, AbortKind, FaultTerminal, WalkResult};
use crate::input::BinaryCtx;
use crate::isa::{
    function_registry, function_registry_lean, insn_to_lean, insn_to_lean_full,
    resolve_call_target_logical, resolve_jump_target,
};
use crate::refinement::{
    emit_descriptor_refinement, emit_refinement, is_const_delta_arm, RefinementCtx,
};
use crate::render;
use crate::spec_call::SpecCall;
use crate::state::SymState;
use crate::transition::{
    emit_transition_fault, emit_transition_path, BItem, FaultTail, RefineTarget, TransitionPathInfo,
};
use crate::witness::build_branch_witness;
use qed_analysis::layout::AccountLayout;
use qed_artifacts::RefinementDescriptor;

/// Generated artifacts and execution facts for one selected program path.
pub struct LiftResult {
    /// Complete Lean module for the bytecode-level path theorem.
    pub lean: String,
    /// Lean module name selected or derived for the lift.
    pub module_name: String,
    /// Size of the executable text section in bytes.
    pub text_bytes: usize,
    /// Number of decoded logical instructions in the program image.
    pub insn_count: usize,
    /// CU count of the lifted triple (`n` in `cuTripleWithinMem n …`).
    /// Surfaced so `--qedmeta` can cross-check the claimed `cu_budget`.
    pub cu: usize,
    /// Optional asm-refines-intrinsic theorem `(module_name, lean)`,
    /// emitted when the arm matches the refinement registry.
    pub refinement: Option<(String, String)>,
    /// Whole-transition path metadata (#40): present when the lift emitted a
    /// `*_transition_path` corollary; feeds `emit_transition_bundle`.
    pub(crate) transition: Option<TransitionPathInfo>,
    /// Shared `.text` module `(module_name, lean)` (batch dedup): emitted when
    /// `shared_text` was requested — the binary's Text/SlotMap/FnRegistry defs,
    /// written ONCE as `Generated/{base}Text.lean` and imported by every arm.
    pub shared_text: Option<(String, String)>,
}

pub(super) type LiftOutput = LiftResult;

/// Optional inputs for one lift. Keeping these named makes call sites
/// auditable and gives us one place to reject incompatible modes.
#[derive(Default)]
/// Optional inputs selecting and refining one path through a program image.
pub struct LiftOptions<'a> {
    /// Instruction discriminator used by the static branch policy.
    pub target_disc: Option<i64>,
    /// Explicit Lean module name; otherwise derived from the program filename.
    pub module_override: Option<String>,
    /// Logical PCs selecting a concrete execution path.
    pub trace: Option<&'a [usize]>,
    /// Instruction name used by registered refinement emitters.
    pub arm_name: Option<&'a str>,
    /// Optional Codama-style IDL value used for account layouts and refinement.
    pub idl: Option<&'a serde_json::Value>,
    /// Recovered logical entry PC for the selected instruction arm.
    pub arm_entry: Option<usize>,
    /// Account layouts recovered from a qedmeta sidecar.
    pub sidecar_layouts: Option<&'a [AccountLayout]>,
    /// Descriptor-driven refinement request.
    pub descriptor: Option<&'a RefinementDescriptor>,
    /// Shared-text module base for large multi-arm lifts.
    pub shared_text: Option<&'a str>,
}

pub(super) type LiftRequest<'a> = LiftOptions<'a>;

impl LiftOptions<'_> {
    fn validate(&self) -> Result<(), LiftError> {
        if self.trace.is_some_and(<[usize]>::is_empty) {
            return Err(LiftError::new(
                DiagnosticKind::TraceInput,
                "qedlift: trace must contain at least one logical PC",
            ));
        }
        if self.module_override.as_deref() == Some("") {
            return Err(LiftError::new(
                DiagnosticKind::UnsupportedConstruct,
                "qedlift: module override must not be empty",
            ));
        }
        if self.shared_text == Some("") {
            return Err(LiftError::new(
                DiagnosticKind::UnsupportedConstruct,
                "qedlift: shared-text module base must not be empty",
            ));
        }
        Ok(())
    }
}

/// Lift without a qedrecover layout sidecar (tests): refinement codegen
/// resolves account layouts from the IDL only. The CLI modes call
/// `lift_one_with_layouts` directly (sidecar layouts / descriptor / shared text).
/// The positional signature deliberately mirrors the historical test fixtures;
/// production callers use the named `LiftRequest` fields above.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(super) fn lift_one(
    so_path: &Path,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    target_disc: Option<i64>,
    module_override: Option<String>,
    trace: Option<&[usize]>,
    arm_name: Option<&str>,
    idl: Option<&serde_json::Value>,
    arm_entry: Option<usize>,
) -> Result<LiftOutput, LiftError> {
    lift_one_with_layouts(
        so_path,
        ctx,
        analysis,
        LiftRequest {
            target_disc,
            module_override,
            trace,
            arm_name,
            idl,
            arm_entry,
            ..LiftRequest::default()
        },
    )
}

pub(super) fn lift_one_with_layouts(
    so_path: &Path,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    request: LiftRequest<'_>,
) -> Result<LiftOutput, LiftError> {
    request.validate()?;
    // Cargo runs a package's unit tests from that package directory. After
    // qedlift became its own workspace crate, fixtures are reached through
    // `../tests`, but generated provenance should remain byte-identical to the
    // public invocation from the qedsvm-rs workspace root.
    #[cfg(test)]
    let emitted_path = so_path
        .strip_prefix("..")
        .ok()
        .filter(|p| p.starts_with("tests/fixtures"))
        .unwrap_or(so_path);
    #[cfg(not(test))]
    let emitted_path = so_path;
    let LiftRequest {
        target_disc,
        module_override,
        trace,
        arm_name,
        idl,
        arm_entry,
        sidecar_layouts,
        descriptor,
        shared_text,
    } = request;
    let insns = &ctx.insns;

    debug_dump_insns(insns);

    let (so_stem, module_name) = derive_module_name(emitted_path, module_override);
    let (out, emit_decode_bridge) = emit_prelude(
        emitted_path,
        ctx,
        analysis,
        &so_stem,
        &module_name,
        shared_text,
    );
    if shared_text.is_some() && emit_decode_bridge {
        return Err(LiftError::new(
            DiagnosticKind::UnsupportedConstruct,
            "qedlift: --shared-text requires the large-text decode-pins \
             path (this binary embeds the full inline decode bridge)",
        ));
    }

    let entry_pc: usize = ctx.executable.get_entrypoint_instruction_offset();
    let WalkResult {
        mut state,
        spec_calls,
        block_pcs,
        exit_pc,
        fault_terminal,
    } = walk_and_exec(ctx, analysis, trace, target_disc, arm_entry, entry_pc)?;

    let out_patched = out.replace(
        "@@HEARTBEATS@@",
        if state.hot_regions.is_empty() {
            "4000000"
        } else {
            "16000000"
        },
    );
    let mut out = out_patched;

    // CR must be a literal `union`-of-`singleton`s (sl_block_auto walks the AST), so inline not def.
    let cr_lean = build_code_req(ctx, analysis, &block_pcs, &state)?;

    // H8 + H2: full bridge omitted for large binaries; pin each walked PC's decode via hex-string embedding
    // + buildSlotMap + native_decide, including call_local PCs resolved through the function registry.
    if !emit_decode_bridge && !block_pcs.is_empty() {
        emit_decode_pins(
            &mut out,
            ctx,
            analysis,
            &block_pcs,
            &state,
            &module_name,
            shared_text,
        )?;
    }

    // Phase 2: Hoare-triple emission. Symbolic execution already done inline above; `state` is ready.
    out.push_str(render::lifted_triple_section_header());
    let tc = assemble_triple(
        &mut state,
        &spec_calls,
        &block_pcs,
        fault_terminal,
        module_name,
        cr_lean,
        entry_pc,
        exit_pc,
    );
    out.push_str(&render::cu_triple_theorem(&render::TripleTheorem {
        name: &tc.lifted_name,
        binders: &tc.theorem_binders,
        n: tc.n,
        m_bound: &tc.m_bound,
        start_pc: tc.start_pc,
        exit_pc: tc.exit_pc,
        cr: &tc.cr_lean,
        pre: &tc.lifted_pre,
        post: &tc.lifted_post,
        rr: &tc.rr,
        proof: &tc.tactic,
    }));

    // H8 satisfiability witness: fail-closed if precondition can't be witnessed satisfiable.
    match build_sat_witness(
        &tc.pre,
        &state,
        &tc.abstractions,
        &tc.abs_subst,
        &tc.folded_rhs,
        &tc.vars,
    ) {
        Ok(w) => out.push_str(&w),
        Err(e) => {
            return Err(e.with_context("qedlift: satisfiability witness construction failed — "))
        }
    }

    // Branch-satisfiability witness (Phase 7.1): certifies h_branch* / h*_lt jointly satisfiable
    // at a concrete assignment (native_decide), closing branch-vacuity. Conservative (non-breaking).
    if let Some(w) = build_branch_witness(&state, &tc.vars) {
        out.push_str(&w);
    }

    emit_heap_corollary(&mut out, &tc, &state);

    // Only counter/vault arms (is_const_delta_arm) — or a spec-driven descriptor, whose
    // `op.add_const` is exactly this const-delta case — get the constant +k cleaning; others stay wrapAdd.
    let counter_arm = is_const_delta_arm(arm_name) || descriptor.is_some();
    let (shifts, post_clean) = clean_balance_shifts(&tc.post, counter_arm);
    emit_balance_corollary(&mut out, &tc, &state, &shifts, &post_clean);

    if let Some(terminal) = fault_terminal {
        emit_fault_corollary(&mut out, &tc, &state, terminal)?;
    }

    let transition: Option<TransitionPathInfo> = match descriptor {
        Some(desc) => emit_transition_corollary(
            &mut out,
            desc,
            &tc,
            &state,
            &shifts,
            &post_clean,
            fault_terminal,
            trace.is_some(),
            insns,
            idl,
            sidecar_layouts,
        ),
        None => None,
    };

    out.push_str(&render::end_namespace(&tc.module_name));

    // ── Asm-refines-intrinsic theorem (mechanized recipe) ───────────
    // Spec-driven descriptor wins when present (the qedspec seam): build the
    // layout-general `AsmRefinesFieldUpdate` straight from the descriptor,
    // bypassing the hardcoded `refine_registry`. Otherwise the registry path.
    let rctx = RefinementCtx {
        lift_module: &tc.module_name,
        pre: &tc.pre,
        post: &post_clean,
        abs_subst: &tc.abs_subst,
        vars: &tc.vars,
        n_cu: tc.n,
        start_pc: tc.start_pc,
        exit_pc: tc.exit_pc,
        idl,
        sidecar_layouts,
    };
    let refinement = match descriptor {
        Some(desc) => emit_descriptor_refinement(desc, rctx),
        None => arm_name.and_then(|arm| emit_refinement(arm, rctx)),
    };

    // Batch dedup: render the shared Text/SlotMap/FnRegistry module the arm's
    // decode pins import (identical for every arm of the same binary).
    let shared_text_out: Option<(String, String)> = shared_text.map(|base| {
        let reg = function_registry(ctx);
        (
            format!("{}Text", base),
            render::shared_text_module(
                base,
                emitted_path,
                ctx.text_bytes.as_slice(),
                &function_registry_lean(&reg),
            ),
        )
    });

    Ok(LiftOutput {
        lean: out,
        module_name: tc.module_name,
        text_bytes: ctx.text_bytes.len(),
        insn_count: insns.len(),
        cu: tc.n,
        refinement,
        transition,
        shared_text: shared_text_out,
    })
}

/// Debug dump of the decoded instruction stream (stderr only; not part of the
/// emitted Lean document).
fn debug_dump_insns(insns: &[ebpf::Insn]) {
    eprintln!("=== decoded insns ===");
    for (i, ins) in insns.iter().enumerate() {
        let rendered = insn_to_lean(ins, i).unwrap_or_else(|e| format!("?? ({})", e));
        eprintln!("  pc={:3}  opc=0x{:02x}  {}", i, ins.opc, rendered);
    }
    eprintln!();
}

/// `(so_stem, module_name)`: the .so file stem and the Lean module name
/// (override, or PascalCase of the stem + `Lifted`).
fn derive_module_name(so_path: &Path, module_override: Option<String>) -> (String, String) {
    let so_stem = so_path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lifted".to_string());
    let module_name = module_override.unwrap_or_else(|| {
        // PascalCase: byte_increment → ByteIncrement
        let mut out = String::new();
        let mut up = true;
        for c in so_stem.chars() {
            if c == '_' || c == '-' {
                up = true;
                continue;
            }
            if up {
                out.extend(c.to_uppercase());
                up = false;
            } else {
                out.push(c);
            }
        }
        format!("{}Lifted", out)
    });
    (so_stem, module_name)
}

/// Emit the module intro + decode-bridge / decoded-insns sections (everything
/// before the walk). Returns `(out, emit_decode_bridge)` — the flag gates the
/// per-PC decode pins later.
fn emit_prelude(
    so_path: &Path,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    so_stem: &str,
    module_name: &str,
    shared_text: Option<&str>,
) -> (String, bool) {
    let text_offset = ctx.text_offset;
    let text_bytes = ctx.text_bytes.as_slice();
    let insns = &ctx.insns;

    // NOT load-bearing for the Hoare triple. Large binaries blow `maxRecDepth` as a ByteArray
    // literal — emit per-PC decode pins (hex-string, H8) above 4096 bytes; small binaries get the full bridge.
    // A modeled syscall ALSO forces the pins path: the small `decodeProgram` bridge renders the raw
    // decode (`.call_local <unresolved>`) for a syscall hash, whereas the pins path threads `syscall_pcs`
    // to render `.call <ctor>` at the syscall PC (matching the spec-call preamble).
    const DECODE_BRIDGE_MAX_BYTES: usize = 4096;
    let has_modeled_syscall = insns
        .iter()
        .any(|ins| ins.opc == ebpf::CALL_IMM && imm_is_modeled_syscall(ins.imm as u32));
    let emit_decode_bridge = text_bytes.len() <= DECODE_BRIDGE_MAX_BYTES && !has_modeled_syscall;

    let decode_claim = render::decode_claim(emit_decode_bridge);
    let mut out = render::module_intro(so_path, decode_claim, so_stem, module_name, shared_text);

    if emit_decode_bridge {
        out.push_str(&render::text_bytearray_defs(
            module_name,
            text_bytes,
            text_offset,
        ));
    } else {
        out.push_str(&render::decode_bridge_omitted_note(
            module_name,
            text_bytes.len(),
            shared_text,
        ));
    }

    // Render the full `.text` as `Array Insn` (sanity, not load-bearing for the Hoare triple).
    // Skip if any opcode can't be rendered — lets us lift a good arm from a partially-modelled binary.
    let mut rendered_insns: Vec<String> = Vec::with_capacity(insns.len());
    let mut decode_skip_reason: Option<String> = None;
    if emit_decode_bridge {
        for (i, insn) in insns.iter().enumerate() {
            let tgt = resolve_call_target_logical(ctx, analysis, insn);
            let jtgt = Some(resolve_jump_target(ctx, i, insn.off as i64));
            match insn_to_lean_full(insn, i, tgt, jtgt) {
                Ok(s) => rendered_insns.push(s),
                Err(e) => {
                    decode_skip_reason = Some(format!("pc={} opc=0x{:02x}: {}", i, insn.opc, e));
                    break;
                }
            }
        }
    }
    if !emit_decode_bridge {
    } else if let Some(reason) = decode_skip_reason {
        out.push_str(&render::decode_renderer_skip_note(module_name, &reason));
    } else {
        // H2: registry resolves call murmur3 imm → .call_local; empty registry fail-closes to .unknown.
        let reg = function_registry(ctx);
        out.push_str(&render::decoded_insns_section(
            module_name,
            &rendered_insns,
            &function_registry_lean(&reg),
        ));
    }

    (out, emit_decode_bridge)
}

/// Render the walked PCs as the literal `CodeReq` union-of-singletons.
fn build_code_req(
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    block_pcs: &[usize],
    state: &SymState,
) -> Result<String, LiftError> {
    let insns = &ctx.insns;

    let cr_lean: String = if block_pcs.is_empty() {
        "CodeReq.empty".to_string()
    } else {
        let mut s = String::new();
        let opens = "(".repeat(block_pcs.len().saturating_sub(1));
        s.push_str(&opens);
        for (i, &pc) in block_pcs.iter().enumerate() {
            // Syscall renders as `.call <ctor>` (not `.call_local`) to match syscall spec's CR singleton.
            let lean_insn = if let Some(ctor) = state.syscall_pcs.get(&pc) {
                format!(".call {}", ctor)
            } else {
                let tgt = resolve_call_target_logical(ctx, analysis, &insns[pc]);
                let jtgt = Some(resolve_jump_target(ctx, pc, insns[pc].off as i64));
                insn_to_lean_full(&insns[pc], pc, tgt, jtgt)?
            };
            if i == 0 {
                s.push_str(&format!("(CodeReq.singleton {} ({}))", pc, lean_insn));
            } else {
                s.push_str(&format!(
                    ".union\n        (CodeReq.singleton {} ({})))",
                    pc, lean_insn
                ));
            }
        }
        s
    };
    Ok(cr_lean)
}

/// H8 + H2: per-PC decode pins for the no-bridge (large / syscall-bearing)
/// path — every walked PC's decode is checked in-kernel by `native_decide`.
fn emit_decode_pins(
    out: &mut String,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    block_pcs: &[usize],
    state: &SymState,
    module_name: &str,
    shared_text: Option<&str>,
) -> Result<(), LiftError> {
    let insns = &ctx.insns;
    let text_bytes = ctx.text_bytes.as_slice();

    let mut pin_offs: Vec<String> = Vec::new();
    let mut pin_exps: Vec<String> = Vec::new();
    for &pc in block_pcs {
        let lean_insn = if let Some(ctor) = state.syscall_pcs.get(&pc) {
            format!(".call {}", ctor)
        } else {
            let tgt = resolve_call_target_logical(ctx, analysis, &insns[pc]);
            let jtgt = Some(resolve_jump_target(ctx, pc, insns[pc].off as i64));
            insn_to_lean_full(&insns[pc], pc, tgt, jtgt)?
        };
        let byte_off = ctx.pc_map.logical_to_slot(pc).expect("logical pc in range") * 8;
        let sz = if insns[pc].opc == 0x18 { 16 } else { 8 };
        pin_offs.push(byte_off.to_string());
        pin_exps.push(format!("some ({}, {})", lean_insn, sz));
    }

    match shared_text {
        // Batch dedup: the Text/SlotMap/FnRegistry defs live in the shared
        // `Generated/{base}Text.lean` module (imported above) — emit only the
        // per-arm pins theorem, referencing the shared defs.
        Some(base) => out.push_str(&render::decode_pins_theorem(
            module_name,
            base,
            &pin_offs,
            &pin_exps,
        )),
        None => {
            // H2: registry resolves call imms to .call_local targets in the pins below.
            let reg = function_registry(ctx);
            out.push_str(&render::large_text_decode_section(
                module_name,
                text_bytes,
                &function_registry_lean(&reg),
                &pin_offs,
                &pin_exps,
            ));
        }
    }
    Ok(())
}

/// Everything the lifted-triple theorem statement is assembled from, shared by
/// the corollary emitters (heap-alloc / balance / typed-fault / transition).
struct TripleCtx {
    module_name: String,
    pre: Vec<Atom>,
    post: Vec<Atom>,
    /// Complex-address abstractions `(param, bridge_hyp, raw_expr)`.
    abstractions: Vec<(String, String, String)>,
    /// Rendered raw expr → abstraction param.
    abs_subst: std::collections::BTreeMap<String, String>,
    /// Bridge-equality RHS with inner abstractions folded, indexed like `abstractions`.
    folded_rhs: Vec<String>,
    /// Symbolic `Nat` parameters (initial regs/cells) in declaration order.
    vars: Vec<String>,
    use_block_iter: bool,
    theorem_binders: String,
    lifted_name: String,
    lifted_pre: String,
    lifted_post: String,
    rr: String,
    cs_atom: &'static str,
    m_bound: String,
    cr_lean: String,
    /// The `_lifted_spec` proof body.
    tactic: String,
    n: usize,
    start_pc: usize,
    exit_pc: usize,
}

/// Theorem-binder assembly: pre/post atoms, complex-address abstractions,
/// symbolic parameters, hypothesis signatures and the proof body — everything
/// `_lifted_spec` and its corollaries are rendered from.
#[allow(clippy::too_many_arguments)]
fn assemble_triple(
    state: &mut SymState,
    spec_calls: &[SpecCall],
    block_pcs: &[usize],
    fault_terminal: Option<FaultTerminal>,
    module_name: String,
    cr_lean: String,
    entry_pc: usize,
    exit_pc: usize,
) -> TripleCtx {
    let mut pre = state.pre.clone();
    let mut post = post_atoms(&pre, state);
    // An OOB fault terminal composes its fault spec against the FRONT of the
    // prefix post (`frame_right` appends the rest on the right), so rotate the
    // spec's region register(s) to the front of both pre and post. Stable —
    // a lift whose region regs already lead (r1[, r2]) is byte-identical.
    if let Some(FaultTerminal::Oob(oob)) = &fault_terminal {
        let spec_regs: Vec<u8> = std::iter::once(oob.region_reg)
            .chain(oob.region_len_reg)
            .collect();
        let rank = |a: &Atom| match a {
            Atom::Reg(r, _) => spec_regs
                .iter()
                .position(|x| x == r)
                .unwrap_or(spec_regs.len()),
            _ => spec_regs.len(),
        };
        pre.sort_by_key(rank);
        post.sort_by_key(rank);
    }

    // Drop `< 2^k` bounds for cells only STORED to (stxdw_spec takes but doesn't bound them).
    state.u64_load_vars.retain(|(v, _)| {
        let h = format!("h{}_lt", v);
        spec_calls.iter().any(|sc| sc.have_line.contains(&h))
    });

    let abstractions = collect_abstractions(&pre);

    let abs_subst: std::collections::BTreeMap<String, String> = abstractions
        .iter()
        .map(|(p, _, e)| (e.clone(), p.clone()))
        .collect();
    let rr = region_req(&pre, state, &abs_subst);
    // call_local requires `callStackIs []` in pre+post (call_local_spec takes it, exit_pops_spec returns it).
    // Net change = none, but sl_block_iter must thread it through the chain.
    let cs_atom = if state.saw_call {
        " ** callStackIs []"
    } else {
        ""
    };

    let vars = collect_pre_vars(&pre);

    let vars_sig = if vars.is_empty() {
        String::new()
    } else {
        format!("({} : Nat)\n    ", vars.join(" "))
    };
    // u64-load bounds: ldxdw_spec leaves `< 2^64` residuals; surface as hyps, discharge with `<;> assumption`.
    let mut u64_hyps = String::new();
    for (v, k) in &state.u64_load_vars {
        u64_hyps.push_str(&format!("(h{}_lt : {} < 2 ^ {})\n    ", v, v, k));
    }
    // Path hyps for conditional jumps (e.g. JeqImm fall-through: `dst ≠ toU64 imm`).
    let mut branch_hyps_sig = String::new();
    for (i, bh) in state.branch_hyps.iter().enumerate() {
        branch_hyps_sig.push_str(&format!("({} : {})\n    ", bh.name(i), bh.lean_hyp()));
    }
    // Memset: ByteArray param + `.size = count` hyp (spec's hbs) + nCu + CU-bound hyp (honest model assumption).
    // Side-condition hyps (e.g. div/mod divisor ≠ 0).
    let mut side_hyps_sig = String::new();
    for (name, prop) in &state.side_hyps {
        side_hyps_sig.push_str(&format!("({} : {})\n    ", name, prop));
    }
    let mut syscall_sig = String::new();
    // Bare `ByteArray` params with no size constraint (e.g. sol_set_return_data's old buffer).
    for ba in &state.bytearray_vars {
        syscall_sig.push_str(&format!("({} : ByteArray)\n    ", ba));
    }
    for (bs, size) in &state.memset_blobs {
        syscall_sig.push_str(&format!("({} : ByteArray)\n    ", bs));
        syscall_sig.push_str(&format!("(h{}_sz : {}.size = {})\n    ", bs, bs, size));
    }
    // Hyps referencing the blob params (e.g. PDA pid.size / off-curve) — after
    // the blob decls so the forward references resolve.
    for (name, prop) in &state.blob_side_hyps {
        syscall_sig.push_str(&format!("({} : {})\n    ", name, prop));
    }
    for (ncu, hcu, ctor) in &state.syscall_cu_vars {
        syscall_sig.push_str(&format!("({} : Nat)\n    ", ncu));
        syscall_sig.push_str(&format!(
            "({} : ∀ s : State, (step (.call {}) s).cuConsumed \
             ≤ s.cuConsumed + {})\n    ",
            hcu, ctor, ncu,
        ));
    }
    // CU bound M = sum of nCu vars; sl_block_iter's cuTripleWithinMem_cast closes via omega.
    let m_bound: String = if state.syscall_cu_vars.is_empty() {
        "0".to_string()
    } else {
        state
            .syscall_cu_vars
            .iter()
            .map(|(n, _, _)| n.clone())
            .collect::<Vec<_>>()
            .join(" + ")
    };
    // `sl_block_auto` now dispatches conditional jumps to their
    // `_not_taken` variants in InstructionSpecs/Jump.lean (see
    // SVM/SBPF/SpecGen.lean), surfacing the path hypothesis as a
    // residual side goal. `<;> assumption` closes them against the
    // theorem's `h_branchK` hypotheses, alongside any u64-load
    // `< 2^64` residuals.
    // A reloaded dword (store-then-reload to the same cell, e.g. a stack
    // spill) surfaces an `hReloadLt_<pc> : v < 2^64` side hyp that
    // `sl_block_auto` leaves as a residual — `<;> assumption` discharges it
    // against the binder. Existing reload-using lifts already trip
    // `u64_load_vars`/`use_block_iter`, so this only flips the reload-only case.
    let has_reload_hyp = state
        .side_hyps
        .iter()
        .any(|(n, _)| n.starts_with("hReloadLt"));
    let needs_assumption =
        !state.branch_hyps.is_empty() || !state.u64_load_vars.is_empty() || has_reload_hyp;
    // Use sl_block_iter when: call_local crossed (sl_block_auto diverges on wrapAdd addresses),
    // any cond-jump taken (SpecGen.mkSpec only has _not_taken; taken arms need explicit spec calls),
    // or a syscall was walked (SpecGen has no `.call <Syscall>` dispatch — the effect is supplied by
    // the emitted `call_<name>_spec` preamble, which only sl_block_iter threads).
    let any_taken = state.branch_hyps.iter().any(|b| b.taken);
    let use_block_iter = state.saw_call || any_taken || !state.syscall_pcs.is_empty();

    let value_gens = build_value_gens(state, &pre, &post, &abs_subst, use_block_iter);
    let tactic = build_proof_body(
        spec_calls,
        &abstractions,
        &value_gens,
        use_block_iter,
        needs_assumption,
    );
    let folded_rhs = fold_bridge_rhs(&abstractions);

    // Abstraction signature (params + bridge equality hyps) for sl_block_iter programs.
    let abs_sig: String = if use_block_iter && !abstractions.is_empty() {
        let mut s = String::new();
        for (param, _, _) in &abstractions {
            s.push_str(&format!("({} : Nat)\n    ", param));
        }
        for (i, (param, h, _)) in abstractions.iter().enumerate() {
            s.push_str(&format!("({} : {} = {})\n    ", h, param, folded_rhs[i]));
        }
        s
    } else {
        String::new()
    };
    let n = block_pcs.len();
    // Start PC = first walked instruction (trace first / static entrypoint / entry_pc fallback).
    let start_pc = block_pcs.first().copied().unwrap_or(entry_pc);

    let theorem_binders = format!(
        "{}{}{}{}{}{}",
        vars_sig, abs_sig, u64_hyps, branch_hyps_sig, side_hyps_sig, syscall_sig,
    );
    let lifted_name = format!("{}_lifted_spec", module_name);
    let lifted_pre = format!("{}{}", atoms_to_lean(&pre, &abs_subst), cs_atom);
    let lifted_post = format!("{}{}", atoms_to_lean(&post, &abs_subst), cs_atom);

    TripleCtx {
        module_name,
        pre,
        post,
        abstractions,
        abs_subst,
        folded_rhs,
        vars,
        use_block_iter,
        theorem_binders,
        lifted_name,
        lifted_pre,
        lifted_post,
        rr,
        cs_atom,
        m_bound,
        cr_lean,
        tactic,
        n,
        start_pc,
        exit_pc,
    }
}

/// Complex addresses (non-InitReg) → opaque Nat params + bridging equalities, so the chain
/// composes over clean atoms (see pda_n1_stack_macro_spec in SVM/SBPF/Macros.lean).
fn collect_abstractions(pre: &[Atom]) -> Vec<(String, String, String)> {
    let mut abstractions: Vec<(String, String, String)> = Vec::new(); // (param, bridge_hyp, raw_expr)

    {
        let mut seen: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        // Flat const address (e.g. lddw heap base) is NOT complex: sl_block_auto re-derives it; abstracting breaks unification.
        let is_const_addr = |e: &Expr| {
            matches!(e, Expr::Const(_))
                || matches!(e, Expr::ToU64(inner) if matches!(inner.as_ref(), Expr::Const(_)))
        };
        for atom in pre {
            if let Atom::Mem { addr_base, .. } = atom {
                if !matches!(addr_base, Expr::InitReg(_)) && !is_const_addr(addr_base) {
                    let rendered = addr_base.to_lean();
                    if !seen.contains_key(&rendered) {
                        let idx = seen.len();
                        seen.insert(rendered.clone(), idx);
                        abstractions.push((
                            format!("addr{}", idx),
                            format!("h_addr{}", idx),
                            rendered,
                        ));
                    }
                }
            }
        }
    }
    abstractions
}

/// Symbolic `Nat` parameters (initial register/cell names) referenced by the
/// pre atoms, in first-reference order.
fn collect_pre_vars(pre: &[Atom]) -> Vec<String> {
    let mut vars: Vec<String> = Vec::new();
    let push_var = |v: &Expr, vars: &mut Vec<String>| {
        if let Expr::InitReg(n) | Expr::InitMem(n) = v {
            if !vars.contains(n) {
                vars.push(n.clone());
            }
        }
    };
    for atom in pre {
        match atom {
            Atom::Reg(_, v) => push_var(v, &mut vars),
            Atom::Mem {
                addr_base, value, ..
            } => {
                push_var(addr_base, &mut vars);
                push_var(value, &mut vars);
            }
            Atom::Bytes32 { addr, .. } => push_var(addr, &mut vars),
            // The blob's `Sym` name is a `ByteArray` (surfaced via
            // `memset_blobs`, not here); the address's Nat leaves were
            // already collected when the syscall's registers were read.
            Atom::Bytes { addr, .. } => push_var(addr, &mut vars),
            // The returnData buffer has no address; its `ByteArray` name is
            // bound via `bytearray_vars`.
            Atom::ReturnData { .. } => {}
        }
    }
    vars
}

// Value abstraction: sl_block_iter re-reduces complex values (wrapAdd/shift/etc.) at every step
// (transferChecked: 178ms→>15min). Generalize to opaque Nat; theorem statement stays concrete.
fn build_value_gens(
    state: &SymState,
    pre: &[Atom],
    post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>,
    use_block_iter: bool,
) -> Vec<String> {
    let value_gens: Vec<String> = if use_block_iter {
        let is_complex = |e: &Expr| match e {
            // All-constant ByteCombo is closed: generalizing triggers kabstract whnf blowup. Leave inline.
            Expr::ByteCombo(vs) => vs.iter().any(|v| !matches!(v, Expr::Const(_))),
            Expr::WrapAdd(..)
            | Expr::WrapSub(..)
            | Expr::WrapMul(..)
            | Expr::NatAdd(..)
            | Expr::Mod(..)
            | Expr::AndU64Imm(..)
            | Expr::LshU64Imm(..)
            | Expr::RshU64Imm(..)
            | Expr::StHalfImm(..)
            | Expr::StWordImm(..)
            | Expr::StDwordImm(..)
            | Expr::Raw(..) => true,
            _ => false,
        };
        let mut seen = std::collections::BTreeSet::new();
        let mut gens = Vec::new();
        for atom in pre.iter().chain(post.iter()) {
            // ↦Bytes blobs have no Nat Expr value (BytesVal, constants only) — skip.
            let v = match atom {
                Atom::Reg(_, v) => v,
                Atom::Mem { value, .. } => value,
                Atom::Bytes { .. } | Atom::Bytes32 { .. } | Atom::ReturnData { .. } => continue,
            };
            if is_complex(v) {
                // Fold sub-expr abstractions first so generalize target matches the sl_rw_abs-folded proof term.
                let r = fold_abstractions(v.to_lean(), abs_subst);
                // Skip address abstractions: generalizing an address rewrites it everywhere, breaking post/rr matching.
                let is_addr_abs = abs_subst.contains_key(&r) || abs_subst.values().any(|p| *p == r);
                // Skip values a syscall spec pins concretely (e.g. sha256's `len`).
                let is_pinned = state.gen_exclude.contains(&r);
                if !is_addr_abs && !is_pinned && seen.insert(r.clone()) {
                    gens.push(r);
                }
            }
        }
        // Longest first: generalize parent before sub-terms to avoid premature clobbering.
        gens.sort_by_key(|e| std::cmp::Reverse(e.len()));
        gens
    } else {
        Vec::new()
    };
    value_gens
}

/// Proof-body emission: the `_lifted_spec` tactic block — spec-call preamble +
/// `sl_rw_abs` + `sl_block_iter` for composed programs, else `sl_block_auto`.
fn build_proof_body(
    spec_calls: &[SpecCall],
    abstractions: &[(String, String, String)],
    value_gens: &[String],
    use_block_iter: bool,
    needs_assumption: bool,
) -> String {
    let tactic: String = if use_block_iter {
        let mut t = String::new();
        for sc in spec_calls {
            t.push_str("  ");
            t.push_str(&sc.have_line);
            t.push('\n');
        }
        // sl_rw_abs: apply innermost-first (shortest raw expr) so inner folds land before outer rw [← h_addrN] can match.
        if !abstractions.is_empty() {
            let mut ordered: Vec<&(String, String, String)> = abstractions.iter().collect();
            ordered.sort_by_key(|(_, _, e)| e.len());
            let abs_names = ordered
                .iter()
                .map(|(_, h, _)| h.clone())
                .collect::<Vec<_>>()
                .join(", ");
            let hyp_names = spec_calls
                .iter()
                .map(|sc| sc.hyp_name.clone())
                .collect::<Vec<_>>()
                .join(", ");
            t.push_str(&format!("  sl_rw_abs [{}] at [{}]\n", abs_names, hyp_names,));
        }
        // Value abstraction as `generalizing [...]` clause — opaque-ification lives in the library tactic.
        let hyp_names = spec_calls
            .iter()
            .map(|sc| sc.hyp_name.clone())
            .collect::<Vec<_>>()
            .join(", ");
        if value_gens.is_empty() {
            t.push_str(&format!("  sl_block_iter [{}]", hyp_names));
        } else {
            t.push_str(&format!(
                "  sl_block_iter [{}] generalizing [{}]",
                hyp_names,
                value_gens.join(", "),
            ));
        }
        t
    } else if needs_assumption {
        // 2-space indent: bare col-0 tactic is absorbed by `open Memory in` as a combinator; indent avoids it.
        "  sl_block_auto <;> assumption".to_string()
    } else {
        "  sl_block_auto".to_string()
    };
    tactic
}

/// Fold inner abstractions inside each bridge RHS so sl_rw_abs doesn't get stuck on partially-expanded
/// patterns (e.g. addr3 = wrapAdd <addr0-expansion> k → wrapAdd addr0 k). Longest-first, strictly-shorter only.
fn fold_bridge_rhs(abstractions: &[(String, String, String)]) -> Vec<String> {
    let folded_rhs: Vec<String> = abstractions
        .iter()
        .map(|(_, _, expr)| {
            let mut inner: Vec<(&String, &String)> = abstractions
                .iter()
                .filter(|(_, _, e)| e.len() < expr.len())
                .map(|(p, _, e)| (e, p))
                .collect();
            inner.sort_by_key(|(e, _)| std::cmp::Reverse(e.len()));
            let mut out = expr.clone();
            for (e, p) in inner {
                out = out.replace(e.as_str(), p.as_str());
            }
            out
        })
        .collect();
    folded_rhs
}

/// Positional arguments for applying `<module>_lifted_spec`, in its binder
/// declaration order (mirrors the signature `assemble_triple` renders).
fn lifted_param_names(tc: &TripleCtx, state: &SymState) -> Vec<String> {
    let mut names: Vec<String> = tc.vars.clone();
    if tc.use_block_iter && !tc.abstractions.is_empty() {
        for (p, _, _) in &tc.abstractions {
            names.push(p.clone());
        }
        for (_, h, _) in &tc.abstractions {
            names.push(h.clone());
        }
    }
    for (v, _) in &state.u64_load_vars {
        names.push(format!("h{}_lt", v));
    }
    for i in 0..state.branch_hyps.len() {
        names.push(format!("h_branch{}", i));
    }
    for (name, _) in &state.side_hyps {
        names.push(name.clone());
    }
    // Mirror `syscall_sig` order: bytearray_vars, memset blobs, blob hyps, CU.
    for ba in &state.bytearray_vars {
        names.push(ba.clone());
    }
    for (bs, _) in &state.memset_blobs {
        names.push(bs.clone());
        names.push(format!("h{}_sz", bs));
    }
    for (name, _) in &state.blob_side_hyps {
        names.push(name.clone());
    }
    for (ncu, hcu, _) in &state.syscall_cu_vars {
        names.push(ncu.clone());
        names.push(hcu.clone());
    }
    names
}

/// Heap-allocation corollary: re-express heap cells via heapBumpPtr/heapBlockU64 predicates
/// (unfold to same memU64Is, so `exact` closes after `simp`). Gated on heap cells; non-heap arms byte-identical.
fn emit_heap_corollary(out: &mut String, tc: &TripleCtx, state: &SymState) {
    let has_heap = tc.pre.iter().chain(tc.post.iter()).any(|a| {
        matches!(a, Atom::Mem { addr_base, addr_off, width, .. }
            if matches!(width, Width::Dword) && heap_cell_addr(addr_base, *addr_off).is_some())
    });
    if !has_heap {
        return;
    }
    // Parameter list in declaration order (mirrors the lift theorem's signature).
    let names = lifted_param_names(tc, state);
    *out = out.replacen(
        "import SVM.SBPF.Macros\n",
        "import SVM.SBPF.Macros\nimport SVM.SBPF.HeapSL\n",
        1,
    );
    let alloc_name = format!("{}_allocates", tc.module_name);
    let alloc_pre = format!(
        "{}{}",
        atoms_to_lean_heap(&tc.pre, &tc.abs_subst),
        tc.cs_atom
    );
    let alloc_post = format!(
        "{}{}",
        atoms_to_lean_heap(&tc.post, &tc.abs_subst),
        tc.cs_atom
    );
    let alloc_proof = render::heap_alloc_proof(&tc.module_name, &names.join(" "));
    out.push_str(&render::cu_triple_theorem(&render::TripleTheorem {
        name: &alloc_name,
        binders: &tc.theorem_binders,
        n: tc.n,
        m_bound: &tc.m_bound,
        start_pc: tc.start_pc,
        exit_pc: tc.exit_pc,
        cr: &tc.cr_lean,
        pre: &alloc_pre,
        post: &alloc_post,
        rr: &tc.rr,
        proof: &alloc_proof,
    }));
}

/// A post-cell whose value wraps two symbolic operands (or a constant delta),
/// re-exposed as clean Nat arithmetic by the balance corollary.
enum Shift {
    Sub(Expr, Expr),
    Add(Expr, Expr),
    AddConst(Expr, i64),
}

/// Detect balance-shaped post cells and clean them: wrapSub/wrapAdd of two
/// InitMem values (and, for counter/vault/descriptor arms, `wrapAdd v (toU64 k)`)
/// become Nat `-`/`+` under funds/no-overflow guards. Returns the shifts and
/// the cleaned post-atom list (other atoms unchanged).
fn clean_balance_shifts(post: &[Atom], counter_arm: bool) -> (Vec<Shift>, Vec<Atom>) {
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    // A constant immediate delta `toU64 k` (e.g. `add64 r2, 1`).
    let const_delta = |e: &Expr| -> Option<i64> {
        if let Expr::ToU64(inner) = e {
            if let Expr::Const(k) = inner.as_ref() {
                return Some(*k);
            }
        }
        None
    };
    let mut shifts: Vec<Shift> = Vec::new();
    let mut post_clean: Vec<Atom> = Vec::with_capacity(post.len());
    for atom in post {
        if let Atom::Mem {
            addr_base,
            addr_off,
            width,
            value,
            delta,
        } = atom
        {
            if let Expr::WrapSub(a, b) = value {
                if is_initmem(a) && is_initmem(b) {
                    shifts.push(Shift::Sub((**a).clone(), (**b).clone()));
                    post_clean.push(Atom::Mem {
                        addr_base: addr_base.clone(),
                        addr_off: *addr_off,
                        width: *width,
                        value: Expr::CleanSub(a.clone(), b.clone()),
                        delta: *delta,
                    });
                    continue;
                }
            }
            if let Expr::WrapAdd(a, b) = value {
                if is_initmem(a) && is_initmem(b) {
                    shifts.push(Shift::Add((**a).clone(), (**b).clone()));
                    post_clean.push(Atom::Mem {
                        addr_base: addr_base.clone(),
                        addr_off: *addr_off,
                        width: *width,
                        value: Expr::NatAdd(a.clone(), b.clone()),
                        delta: *delta,
                    });
                    continue;
                }
                if counter_arm && is_initmem(a) {
                    if let Some(k) = const_delta(b) {
                        shifts.push(Shift::AddConst((**a).clone(), k));
                        post_clean.push(Atom::Mem {
                            addr_base: addr_base.clone(),
                            addr_off: *addr_off,
                            width: *width,
                            value: Expr::NatAdd(a.clone(), Box::new(Expr::Const(k))),
                            delta: *delta,
                        });
                        continue;
                    }
                }
            }
        }
        post_clean.push(atom.clone());
    }
    (shifts, post_clean)
}

/// Balance-correctness corollary: re-expose wrapSub/wrapAdd as Nat arithmetic under
/// funds/no-overflow guards. Only cells wrapping two InitMem values qualify (excludes reg/addr arithmetic).
fn emit_balance_corollary(
    out: &mut String,
    tc: &TripleCtx,
    state: &SymState,
    shifts: &[Shift],
    post_clean: &[Atom],
) {
    if shifts.is_empty() {
        return;
    }
    let abs_subst = &tc.abs_subst;
    // Param names in signature order (vars → abstraction params/hyps → u64 bounds → branch hyps → syscall).
    let names = lifted_param_names(tc, state);

    let mut extra_hyps = String::new();
    let mut rw_terms: Vec<String> = Vec::new();
    for (k, sh) in shifts.iter().enumerate() {
        match sh {
            Shift::Sub(a, b) => {
                let al = fold_abstractions(a.to_lean(), abs_subst);
                let bl = fold_abstractions(b.to_lean(), abs_subst);
                extra_hyps.push_str(&format!("(h_funds{} : {} ≤ {})\n    ", k, bl, al));
                extra_hyps.push_str(&format!("(h_src_lt{} : {} < 2 ^ 64)\n    ", k, al));
                rw_terms.push(format!("← wrapSub_of_le h_funds{} h_src_lt{}", k, k));
            }
            Shift::Add(a, b) => {
                let al = fold_abstractions(a.to_lean(), abs_subst);
                let bl = fold_abstractions(b.to_lean(), abs_subst);
                extra_hyps.push_str(&format!("(h_noovf{} : {} + {} < 2 ^ 64)\n    ", k, al, bl));
                rw_terms.push(format!("← wrapAdd_of_lt h_noovf{}", k));
            }
            Shift::AddConst(a, c) => {
                // Clean `wrapAdd a (toU64 k) → a + k` under the no-overflow hyp.
                // `+1` keeps the specialized `wrapAdd_one_of_lt` so every existing
                // +1 lift stays byte-identical; any other positive literal uses the
                // general `wrapAdd_const_of_lt`.
                let al = fold_abstractions(a.to_lean(), abs_subst);
                extra_hyps.push_str(&format!("(h_noovf{} : {} + {} < 2 ^ 64)\n    ", k, al, c));
                if *c == 1 {
                    rw_terms.push(format!("← wrapAdd_one_of_lt h_noovf{}", k));
                } else {
                    rw_terms.push(format!("← wrapAdd_const_of_lt h_noovf{}", k));
                }
            }
        }
    }

    let balance_name = format!("{}_balance_correct", tc.module_name);
    let balance_binders = format!("{}{}", tc.theorem_binders, extra_hyps);
    let balance_pre = format!("{}{}", atoms_to_lean(&tc.pre, abs_subst), tc.cs_atom);
    let balance_post = format!("{}{}", atoms_to_lean(post_clean, abs_subst), tc.cs_atom);
    let balance_proof =
        render::balance_proof(&tc.module_name, &names.join(" "), &rw_terms.join(", "));
    out.push_str(&render::cu_triple_theorem(&render::TripleTheorem {
        name: &balance_name,
        binders: &balance_binders,
        n: tc.n,
        m_bound: &tc.m_bound,
        start_pc: tc.start_pc,
        exit_pc: tc.exit_pc,
        cr: &tc.cr_lean,
        pre: &balance_pre,
        post: &balance_post,
        rr: &tc.rr,
        proof: &balance_proof,
    }));
}

// Typed-fault corollary (Phase 7 sub-item 3): the walked happy path ends in
// a typed fault. Compose the running prefix (`<module>_lifted_spec`, a
// `cuTripleWithinMem`) with the terminal fault spec, surfacing `vmError`
// (audit L1's typed channel). The fault PC is the walk's `exit_pc` (the
// terminal is NOT in `block_pcs`); disjointness of the prefix CodeReq from
// the singleton fault CodeReq folds `Disjoint_union_left` over
// `singleton_disjoint_singleton` (every prefix PC ≠ the fault PC).
//   - Abort/panic: unconditional `.abort`, pre-parametric tail, `seq_fault_pure`.
//   - OOB syscall: conditional `.accessViolation`; the tail reads the region
//     register, so the single-register fault-spec pre is `frame_right`-extended
//     to the prefix post and sequenced via the Mem-Mem `seq_fault` (combined
//     `rr = prefixRR ∧ OOB`).
fn emit_fault_corollary(
    out: &mut String,
    tc: &TripleCtx,
    state: &SymState,
    terminal: FaultTerminal,
) -> Result<(), LiftError> {
    let abs_subst = &tc.abs_subst;
    let post = &tc.post;
    let lifted_name = &tc.lifted_name;
    let lifted_pre = &tc.lifted_pre;
    let lifted_post = &tc.lifted_post;
    let theorem_binders = &tc.theorem_binders;
    let m_bound = &tc.m_bound;
    let rr = &tc.rr;
    let cs_atom = tc.cs_atom;
    let cr_lean = &tc.cr_lean;
    let (n, start_pc, exit_pc) = (tc.n, tc.start_pc, tc.exit_pc);
    // Param names in `_lifted_spec` signature order (mirrors heap/balance).
    let names = lifted_param_names(tc, state);
    let fault_name = format!("{}_fault_correct", tc.module_name);

    let fault_ctor = match terminal {
        FaultTerminal::Abort(k) => k.ctor(),
        FaultTerminal::Oob(o) => o.ctor,
    };
    let cr_fault = format!(
        "({}).union\n        (CodeReq.singleton {} (.call {}))",
        cr_lean, exit_pc, fault_ctor,
    );
    let (n_cu, fault_binders, fault_rr, vm_error, fault_proof) = match terminal {
        FaultTerminal::Abort(kind) => {
            let ctor = kind.ctor();
            let binders = format!(
                "{}(nCuAbort : Nat)\n    (hCuAbort : ∀ s : State,\n        \
                 (step (.call {}) s).cuConsumed ≤ s.cuConsumed + nCuAbort)\n    ",
                theorem_binders, ctor,
            );
            let proof = format!(
                "  refine cuTripleWithinMem_seq_fault_pure ?_ ({lifted} {names}) \
                 ({spec} ({post}) {pc} nCuAbort hCuAbort)\n  \
                 repeat' apply CodeReq.Disjoint_union_left\n  \
                 all_goals exact CodeReq.singleton_disjoint_singleton _ _ (by decide)",
                lifted = lifted_name,
                names = names.join(" "),
                spec = kind.faults_spec(),
                post = lifted_post,
                pc = exit_pc,
            );
            let _ = ctor;
            (
                format!("{} + nCuAbort", m_bound),
                binders,
                rr.clone(),
                kind.vm_error(),
                proof,
            )
        }
        FaultTerminal::Oob(oob) => {
            // OOB needs the prefix post free of a callStack atom (no
            // call_local) so the frame's `rest` is exactly the non-region
            // post atoms, and the region register must be the FIRST post
            // atom (frame_right adds `rest` on the right).
            if !cs_atom.is_empty() {
                return Err(LiftError::new(
                    DiagnosticKind::UnsupportedConstruct,
                    "qedlift: OOB fault terminal with a callStack atom \
                     (call_local prefix) is not yet supported",
                ));
            }
            let region_value = post
                .iter()
                .find_map(|a| match a {
                    Atom::Reg(r, v) if *r == oob.region_reg => Some(v.clone()),
                    _ => None,
                })
                .ok_or_else(|| {
                    LiftError::new(
                        DiagnosticKind::UnsupportedConstruct,
                        format!(
                            "qedlift: OOB fault terminal reads r{} but it is absent from \
                 the lifted post",
                            oob.region_reg
                        ),
                    )
                })?;
            if !matches!(post.first(), Some(Atom::Reg(r, _)) if *r == oob.region_reg) {
                return Err(LiftError::new(
                    DiagnosticKind::UnsupportedConstruct,
                    format!(
                        "qedlift: OOB fault terminal needs r{} as the first post \
                     atom (frame_right arrangement)",
                        oob.region_reg
                    ),
                ));
            }
            // Register-sized region (e.g. sol_set_return_data's
            // `[r1, r1+r2)`): the spec's pre is a two-atom sepConj, so the
            // length register must be the SECOND post atom; its literal
            // side conditions (≤ cap, ≠ 0) discharge `by decide` at the
            // traced value.
            let len_value = match oob.region_len_reg {
                None => None,
                Some(lr) => {
                    if !matches!(post.get(1), Some(Atom::Reg(r, _)) if *r == lr) {
                        return Err(LiftError::new(
                            DiagnosticKind::UnsupportedConstruct,
                            format!(
                                "qedlift: register-sized OOB region needs r{} as \
                             the second post atom",
                                lr
                            ),
                        ));
                    }
                    post.iter().find_map(|a| match a {
                        Atom::Reg(r, v) if *r == lr => Some(v.clone()),
                        _ => None,
                    })
                }
            };
            let r1v = fold_abstractions(region_value.to_lean(), abs_subst);
            let lenv = len_value.map(|v| fold_abstractions(v.to_lean(), abs_subst));
            let spec_args = match &lenv {
                None => format!("({r1v})"),
                Some(l) => format!("({r1v}) ({l}) (by decide) (by decide)"),
            };
            let spec_regs: Vec<u8> = std::iter::once(oob.region_reg)
                .chain(oob.region_len_reg)
                .collect();
            let rest_atoms: Vec<Atom> = post
                .iter()
                .filter(|a| !matches!(a, Atom::Reg(r, _) if spec_regs.contains(r)))
                .cloned()
                .collect();
            // The fault tail spec, framed to the prefix post when there is a
            // non-region remainder (else applied bare — pre is exactly the
            // spec's region atoms).
            let tail = if rest_atoms.is_empty() {
                format!(
                    "({spec} {args} {pc} nCuOob hCuOob)",
                    spec = oob.faults_spec,
                    args = spec_args,
                    pc = exit_pc
                )
            } else {
                let rest_lean = atoms_to_lean(&rest_atoms, abs_subst);
                format!(
                    "(cuTripleFaultsWithinMem_frame_right ({rest})\n      \
                     (by repeat' apply pcFree_sepConj\n          \
                     all_goals first\n            | exact pcFree_regIs _ _\n            \
                     | exact pcFree_memU64Is _ _\n            \
                     | exact pcFree_memU32Is _ _\n            \
                     | exact pcFree_memU16Is _ _\n            \
                     | exact pcFree_memByteIs _ _\n            \
                     | exact pcFree_memBytes32Is _ _\n            \
                     | exact pcFree_memBytesIs _ _)\n      \
                     ({spec} {args} {pc} nCuOob hCuOob))",
                    rest = rest_lean,
                    spec = oob.faults_spec,
                    args = spec_args,
                    pc = exit_pc,
                )
            };
            let binders = format!(
                "{}(nCuOob : Nat)\n    (hCuOob : ∀ s : State,\n        \
                 (step (.call {}) s).cuConsumed ≤ s.cuConsumed + nCuOob)\n    ",
                theorem_binders, oob.ctor,
            );
            // Combined rr: prefix region requirement ∧ the OOB condition
            // (write guard → `containsWritable`, read guard → `containsRange`;
            // must match the syscall's `faults_oob` triple).
            let region_pred = if oob.region_writable {
                "containsWritable"
            } else {
                "containsRange"
            };
            let region_len = match &lenv {
                None => oob.region_size.to_string(),
                Some(l) => format!("({l})"),
            };
            let combined_rr = format!(
                "({}) ∧ rt.{} ({}) {} = false",
                rr, region_pred, r1v, region_len,
            );
            let proof = format!(
                "  refine cuTripleWithinMem_seq_fault ?_ ({lifted} {names}) {tail}\n  \
                 repeat' apply CodeReq.Disjoint_union_left\n  \
                 all_goals exact CodeReq.singleton_disjoint_singleton _ _ (by decide)",
                lifted = lifted_name,
                names = names.join(" "),
                tail = tail,
            );
            (
                format!("{} + nCuOob", m_bound),
                binders,
                combined_rr,
                ".accessViolation",
                proof,
            )
        }
    };
    let n_steps = format!("{} + 1", n);
    out.push_str(&render::faults_triple_theorem(&render::FaultsTriple {
        name: &fault_name,
        binders: &fault_binders,
        n_steps: &n_steps,
        n_cu: &n_cu,
        entry: start_pc,
        cr: &cr_fault,
        pre: lifted_pre,
        rr: &fault_rr,
        vm_error,
        proof: &fault_proof,
    }));
    Ok(())
}

// ── Whole-transition path corollary (#40 gap 1) ─────────────────
// Trace-guided + descriptor-driven walk landing on the shared `.exit`:
// compose the running triple (`*_balance_correct` when the mutated cell
// was overflow-cleaned, else `*_lifted_spec`) with the `.exit` into an
// `AsmRefinesTransitionPath` obligation over the descriptor's layout.
// Fail-closed: binder kinds outside {vars, abstraction bridges, u64
// bounds, branch guards, side hyps, shift guards} skip the corollary,
// as does a call_local prefix (callStack atom) or a fault terminal.
#[allow(clippy::too_many_arguments)]
fn emit_transition_corollary(
    out: &mut String,
    desc: &RefinementDescriptor,
    tc: &TripleCtx,
    state: &SymState,
    shifts: &[Shift],
    post_clean: &[Atom],
    fault_terminal: Option<FaultTerminal>,
    has_trace: bool,
    insns: &[ebpf::Insn],
    idl: Option<&serde_json::Value>,
    sidecar_layouts: Option<&[AccountLayout]>,
) -> Option<TransitionPathInfo> {
    let abs_subst = &tc.abs_subst;
    let pre: &[Atom] = &tc.pre;
    let post: &[Atom] = &tc.post;
    let module_name = &tc.module_name;
    let lifted_name = &tc.lifted_name;
    let theorem_binders = &tc.theorem_binders;
    let vars = &tc.vars;
    let use_block_iter = tc.use_block_iter;
    let abstractions = &tc.abstractions;
    let folded_rhs = &tc.folded_rhs;
    let m_bound = &tc.m_bound;
    let rr = &tc.rr;
    let cs_atom = tc.cs_atom;
    let cr_lean = &tc.cr_lean;
    let (n, start_pc, exit_pc) = (tc.n, tc.start_pc, tc.exit_pc);
    let mut transition: Option<TransitionPathInfo> = None;

    // Terminal kind: a clean `.exit` (error/success return) or a typed
    // abort/panic fault. OOB fault terminals fall closed for now.
    let wired_binders = has_trace
        && cs_atom.is_empty()
        && state.bytearray_vars.is_empty()
        && state.memset_blobs.is_empty()
        && state.blob_side_hyps.is_empty()
        && state.syscall_cu_vars.is_empty();
    let terminal_fault = matches!(fault_terminal,
        Some(FaultTerminal::Abort(k))
            if !matches!(k, AbortKind::Invoke | AbortKind::InvokeC));
    let terminal_oob = matches!(fault_terminal, Some(FaultTerminal::Oob(_)));
    let terminal_exit = wired_binders
        && fault_terminal.is_none()
        && insns
            .get(exit_pc)
            .map(|i| i.opc == ebpf::EXIT)
            .unwrap_or(false);
    if terminal_exit || (wired_binders && (terminal_fault || terminal_oob)) {
        // Binder metadata + positional args in `_lifted_spec` signature order.
        let mut bitems: Vec<BItem> = vars.iter().cloned().map(BItem::Val).collect();
        let mut names: Vec<String> = vars.clone();
        if use_block_iter && !abstractions.is_empty() {
            for (p, _, _) in abstractions {
                bitems.push(BItem::Val(p.clone()));
                names.push(p.clone());
            }
            for (i, (param, h, _)) in abstractions.iter().enumerate() {
                bitems.push(BItem::Hyp {
                    name: h.clone(),
                    prop: format!("{} = {}", param, folded_rhs[i]),
                });
                names.push(h.clone());
            }
        }
        for (v, k) in &state.u64_load_vars {
            bitems.push(BItem::Hyp {
                name: format!("h{}_lt", v),
                prop: format!("{} < 2 ^ {}", v, k),
            });
            names.push(format!("h{}_lt", v));
        }
        for (i, bh) in state.branch_hyps.iter().enumerate() {
            bitems.push(BItem::Guard {
                prop: bh.lean_hyp(),
            });
            names.push(bh.name(i));
        }
        for (name, prop) in &state.side_hyps {
            bitems.push(BItem::Hyp {
                name: name.clone(),
                prop: prop.clone(),
            });
            names.push(name.clone());
        }
        // Target: the balance-corrected triple when shifts were cleaned
        // (its post carries the clean `+`/`-` field value).
        let (t_name, t_binders, t_post) = if shifts.is_empty() {
            (lifted_name.clone(), theorem_binders.clone(), post)
        } else {
            let mut extra = String::new();
            for (k, sh) in shifts.iter().enumerate() {
                match sh {
                    Shift::Sub(a, b) => {
                        let al = fold_abstractions(a.to_lean(), abs_subst);
                        let bl = fold_abstractions(b.to_lean(), abs_subst);
                        extra.push_str(&format!("(h_funds{} : {} ≤ {})\n    ", k, bl, al));
                        extra.push_str(&format!("(h_src_lt{} : {} < 2 ^ 64)\n    ", k, al));
                        bitems.push(BItem::Hyp {
                            name: format!("h_funds{}", k),
                            prop: format!("{} ≤ {}", bl, al),
                        });
                        bitems.push(BItem::Hyp {
                            name: format!("h_src_lt{}", k),
                            prop: format!("{} < 2 ^ 64", al),
                        });
                        names.push(format!("h_funds{}", k));
                        names.push(format!("h_src_lt{}", k));
                    }
                    Shift::Add(a, b) => {
                        let al = fold_abstractions(a.to_lean(), abs_subst);
                        let bl = fold_abstractions(b.to_lean(), abs_subst);
                        extra.push_str(&format!("(h_noovf{} : {} + {} < 2 ^ 64)\n    ", k, al, bl));
                        bitems.push(BItem::Hyp {
                            name: format!("h_noovf{}", k),
                            prop: format!("{} + {} < 2 ^ 64", al, bl),
                        });
                        names.push(format!("h_noovf{}", k));
                    }
                    Shift::AddConst(a, c) => {
                        let al = fold_abstractions(a.to_lean(), abs_subst);
                        extra.push_str(&format!("(h_noovf{} : {} + {} < 2 ^ 64)\n    ", k, al, c));
                        bitems.push(BItem::Hyp {
                            name: format!("h_noovf{}", k),
                            prop: format!("{} + {} < 2 ^ 64", al, c),
                        });
                        names.push(format!("h_noovf{}", k));
                    }
                }
            }
            (
                format!("{}_balance_correct", module_name),
                format!("{}{}", theorem_binders, extra),
                post_clean,
            )
        };
        let tctx = RefinementCtx {
            lift_module: module_name,
            pre,
            post: t_post,
            abs_subst,
            vars,
            n_cu: n,
            start_pc,
            exit_pc,
            idl,
            sidecar_layouts,
        };
        let t_args = names.join(" ");
        let target = RefineTarget {
            name: &t_name,
            args: &t_args,
            binders: &t_binders,
            bitems,
        };
        let emitted = if terminal_fault || terminal_oob {
            let t_post_s = format!("{}{}", atoms_to_lean(t_post, abs_subst), cs_atom);
            let (ctor, spec, oob_info) = match fault_terminal {
                Some(FaultTerminal::Abort(k)) => (k.ctor(), k.faults_spec(), None),
                Some(FaultTerminal::Oob(o)) => (
                    o.ctor,
                    o.faults_spec,
                    Some((o.region_reg, o.region_size, o.region_writable)),
                ),
                _ => unreachable!("gated on a fault terminal"),
            };
            emit_transition_fault(
                desc,
                tctx,
                target,
                m_bound,
                cr_lean,
                rr,
                FaultTail {
                    ctor,
                    spec,
                    oob: oob_info,
                    target_post: &t_post_s,
                },
            )
        } else {
            emit_transition_path(desc, tctx, target, m_bound, cr_lean, rr)
        };
        if let Some((text, info)) = emitted {
            out.push_str(&text);
            *out = out.replace(
                "import SVM.SBPF.SatWitness",
                "import SVM.SBPF.SatWitness\nimport SVM.Solana.Abstract.Transition",
            );
            transition = Some(info);
        }
    }
    transition
}
