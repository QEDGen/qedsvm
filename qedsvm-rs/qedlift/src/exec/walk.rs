use solana_sbpf::{ebpf, static_analysis::Analysis};

use crate::diagnostic::{DiagnosticKind, LiftError};
use crate::input::BinaryCtx;
use crate::isa::{resolve_call_target_logical, resolve_jump_target};
use crate::spec_call::{spec_call_for, SpecCall};
use crate::state::SymState;

use super::control::{is_cond_jump_opc, resolve_branch_taken, TraceCursor};
use super::step::step;
use super::syscall_registry::{
    classify_call_imm, dispatch_traced_syscall, AbortKind, CallImmClassification, OobSyscall,
};

/// What terminated the walked happy path with a typed fault.
#[derive(Clone, Copy)]
pub(crate) enum FaultTerminal {
    Abort(AbortKind),
    Oob(OobSyscall),
}

/// What the CFG walk + symbolic execution produced for one arm: the final
/// symbolic state, the per-insn spec calls, the walked PCs, the terminator PC
/// and (when the path ends in an abort-style terminal) the typed fault.
pub(crate) struct WalkResult {
    pub(crate) state: SymState,
    pub(crate) spec_calls: Vec<SpecCall>,
    pub(crate) block_pcs: Vec<usize>,
    pub(crate) exit_pc: usize,
    pub(crate) fault_terminal: Option<FaultTerminal>,
}

#[derive(Debug, Eq, PartialEq)]
pub(super) enum ExitDisposition {
    TopLevel,
    NestedReturn,
}

pub(super) fn exit_disposition(state: &SymState) -> ExitDisposition {
    if state.call_stack.is_empty() {
        ExitDisposition::TopLevel
    } else {
        ExitDisposition::NestedReturn
    }
}

pub(super) fn merge_blob_splits(
    blob_splits: &mut std::collections::BTreeMap<(String, i64), i64>,
    new_blob_splits: impl IntoIterator<Item = (String, i64, i64)>,
) {
    for (root, lo, n) in new_blob_splits {
        blob_splits.insert((root, lo), n);
    }
}

pub(super) fn merge_hot_regions(
    hot_regions: &mut std::collections::BTreeMap<String, Vec<(i64, i64)>>,
    new_hot: impl IntoIterator<Item = (String, i64, i64)>,
) {
    for (root, lo, hi) in new_hot {
        let regions = hot_regions.entry(root).or_default();
        let (mut merged_lo, mut merged_hi) = (lo, hi);
        regions.retain(|(existing_lo, existing_hi)| {
            if *existing_lo <= merged_hi && merged_lo <= *existing_hi {
                merged_lo = merged_lo.min(*existing_lo);
                merged_hi = merged_hi.max(*existing_hi);
                false
            } else {
                true
            }
        });
        regions.push((merged_lo, merged_hi));
    }
}

pub(crate) struct WalkOptions<'a> {
    pub(crate) trace: Option<&'a [usize]>,
    pub(crate) target_discriminator: Option<i64>,
    pub(crate) arm_entry: Option<usize>,
    pub(crate) program_entry: usize,
}

/// CFG walk + symbolic execution + the hot-region/blob-split retry loop +
/// syscall dispatch. Straight-line→pc+1, ja→target, cond-jump→fall-through,
/// call_local→push+jump, exit/empty-stack→done, exit/non-empty→pop+resume.
/// Starts at ELF entrypoint (NOT analysis PC 0: linker may place helpers
/// before it).
pub(crate) fn walk_and_exec(
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    options: WalkOptions<'_>,
) -> Result<WalkResult, LiftError> {
    let insns = &ctx.insns;
    let WalkOptions {
        trace,
        target_discriminator,
        arm_entry,
        program_entry,
    } = options;

    // Hot regions: grow monotonically across walk retries (H8 Phase B); attempt cap is a safety net.
    let mut hot_regions: std::collections::BTreeMap<String, Vec<(i64, i64)>> = Default::default();
    let mut blob_splits: std::collections::BTreeMap<(String, i64), i64> = Default::default();
    let mut walk_attempts = 0usize;
    loop {
        walk_attempts += 1;
        if walk_attempts > 8 {
            return Err(LiftError::new(
                DiagnosticKind::Other,
                "qedlift: hot-region demotion did not converge after 8 walk retries",
            ));
        }
        let mut spec_calls: Vec<SpecCall> = Vec::new();

        let mut block_pcs: Vec<usize> = Vec::new();
        let exit_pc: usize;
        // Phase 7 sub-item 3: when the walked happy-path terminates in a typed
        // fault (`.call .abort`/`.sol_panic_` ⇒ `.abort`, or an out-of-bounds
        // syscall ⇒ `.accessViolation`), record it here so the emitter renders a
        // `*_fault_correct` corollary (`cuTripleFaultsWithinMem`) instead of only a
        // success triple. `None` = ordinary `exit` terminator (the success case).
        let mut fault_terminal: Option<FaultTerminal> = None;
        let mut state = SymState {
            hot_regions: hot_regions.clone(),
            blob_splits: blob_splits.clone(),
            ..SymState::default()
        };
        {
            let mut trace_cursor = trace.map(TraceCursor::new).transpose()?;
            let mut pc_iter: usize = match trace_cursor.as_ref() {
                Some(cursor) => {
                    // #41 Phase 4: cross-check sidecar arm_entry_pc is on the trace (mismatch → fail-closed).
                    if let Some(arm) = arm_entry {
                        if !cursor.contains(arm) {
                            return Err(LiftError::new(
                                DiagnosticKind::TraceInput,
                                format!(
                                    "qedmeta/trace mismatch: recovered arm_entry_pc {} \
                             is not on the execution trace (the sidecar describes \
                             a different arm than the trace executes)",
                                    arm
                                ),
                            ));
                        }
                    }
                    cursor.current().expect("TraceCursor rejects empty traces")
                }
                // #41 Phase 4: seed from recovered arm_entry (no disc-cascade nav); fallback = entry_pc.
                None => arm_entry.unwrap_or(program_entry),
            };
            // Walk cap: prevents runaway on unmodelled back-branches; generous for deep dispatcher cascades.
            let walk_cap = trace_cursor.as_ref().map_or(1024, TraceCursor::walk_cap);
            let mut walk_steps: usize = 0;
            loop {
                walk_steps += 1;
                if walk_steps > walk_cap {
                    return Err(LiftError::new(
                        DiagnosticKind::WalkerSteps,
                        format!(
                            "walker exceeded {} steps at pc={} (likely back-branch \
                     defaulted to fall-through)",
                            walk_cap, pc_iter
                        ),
                    ));
                }
                if let Some(cursor) = trace_cursor.as_ref() {
                    let Some(current) = cursor.current() else {
                        exit_pc = pc_iter;
                        break;
                    };
                    pc_iter = current;
                }
                if pc_iter >= insns.len() {
                    exit_pc = pc_iter;
                    break;
                }
                let ins = &insns[pc_iter];

                // EXIT: nested return (pop call stack + restore r6..r10) or top-level terminator.
                if ins.opc == ebpf::EXIT {
                    if exit_disposition(&state) == ExitDisposition::TopLevel {
                        exit_pc = pc_iter;
                        break;
                    } else {
                        block_pcs.push(pc_iter);
                        // Emit spec call BEFORE popping (r6..r10 still at callee-frame values).
                        if let Some(sc) =
                            spec_call_for(&state, ins, pc_iter, None, None, None, None)
                        {
                            spec_calls.push(sc);
                        }
                        let (call_pc, saved) = state.call_stack.pop().unwrap();
                        // Mirror exit_pops_spec: restore saved r6..r10 so post-state matches (callee may have clobbered them).
                        for (i, r) in (6u8..=10).enumerate() {
                            state.write_reg(r, saved[i].clone());
                        }
                        // Trace: next PC from trace; static: jump to callpc+1.
                        if let Some(cursor) = trace_cursor.as_mut() {
                            cursor.advance();
                        } else {
                            pc_iter = call_pc + 1;
                        }
                        continue;
                    }
                }

                // Typed-fault terminal (Phase 7 sub-item 3): `.call .abort` /
                // `.call .sol_panic_` never return, so they end the walk like
                // `exit` — but with the typed `vmError` channel (audit L1).
                // `sol_invoke_signed` ALSO terminates the walk (proof-side CPI is
                // the fail-closed `Cpi.exec` stub → `.unsupportedInstruction`),
                // even though the runner's trace continues past it. The terminal
                // is NOT pushed to `block_pcs` (it is the fault tail, composed by
                // the emitter via `call_<kind>_faults_spec`, not the prefix).
                if ins.opc == ebpf::CALL_IMM {
                    let imm = ins.imm as u32;
                    if let Some(kind) = AbortKind::from_hash(imm) {
                        fault_terminal = Some(FaultTerminal::Abort(kind));
                        exit_pc = pc_iter;
                        break;
                    }
                    // OOB (H6) syscall fault: a known guard-checked syscall that, on
                    // this trace, does NOT return to pc+1 (the OOB access is stuck).
                    // Trace-only: in static mode the same syscall might succeed.
                    if let Some(oob) = OobSyscall::from_hash(imm) {
                        if let Some(cursor) = trace_cursor.as_ref() {
                            if cursor.next() != Some(pc_iter + 1) {
                                fault_terminal = Some(FaultTerminal::Oob(oob));
                                exit_pc = pc_iter;
                                break;
                            }
                        }
                    }
                }

                // Syscall (trace): call_imm returning to pc+1 (no BPF frame push) → dispatch on hash.
                if ins.opc == ebpf::CALL_IMM {
                    if let Some(cursor) = trace_cursor.as_mut() {
                        if cursor.next() == Some(pc_iter + 1) {
                            let imm = ins.imm as u32;
                            dispatch_traced_syscall(
                                &mut state,
                                &mut spec_calls,
                                &mut block_pcs,
                                pc_iter,
                                imm,
                                ctx,
                            )?;
                            cursor.advance();
                            continue;
                        }
                    }
                }

                block_pcs.push(pc_iter);
                let call_target = resolve_call_target_logical(ctx, analysis, ins);
                // Branch hyp name indexed by number of branches seen so far.
                let branch_idx = state.branch_hyps.len();
                let branch_hyp = format!("h_branch{}", branch_idx);
                let is_cond_jump = is_cond_jump_opc(ins.opc);
                let branch_hyp_for_call = if is_cond_jump {
                    Some(branch_hyp.as_str())
                } else {
                    None
                };
                // Slot-relative offset → logical PC (handles lddw 2-slot encoding); shared by spec + walk.
                let jtgt = resolve_jump_target(ctx, pc_iter, ins.off as i64);
                // Trace: taken iff next PC ≠ pc+1; target mismatch vs decoded offset = fail-closed.
                // Static: discriminator-driven where possible, else fall-through.
                let branch_decision = resolve_branch_taken(
                    trace_cursor.as_ref(),
                    pc_iter,
                    ins,
                    jtgt,
                    is_cond_jump,
                    target_discriminator,
                )?;
                let branch_taken = branch_decision.as_option();

                if let Some(sc) = spec_call_for(
                    &state,
                    ins,
                    pc_iter,
                    call_target,
                    branch_hyp_for_call,
                    branch_taken,
                    Some(jtgt),
                ) {
                    spec_calls.push(sc);
                }
                step(&mut state, ins, Some(pc_iter), branch_taken)?;
                // Phase A aliasing: surface address equation for same-cell different-rendering (consumed by rw [h_alias_<pc>]).
                if let Some((lhs, rhs)) = state.pending_alias.take() {
                    state
                        .side_hyps
                        .push((format!("h_alias_{}", pc_iter), format!("{} = {}", lhs, rhs)));
                }
                for (i, (lhs, rhs)) in state.pending_slot_aliases.drain(..).enumerate() {
                    state.side_hyps.push((
                        format!("h_alias_{}_{}", pc_iter, i),
                        format!("{} = {}", lhs, rhs),
                    ));
                }

                if let Some(cursor) = trace_cursor.as_mut() {
                    cursor.advance();
                    continue;
                }
                match ins.opc {
                    ebpf::JA => {
                        pc_iter = jtgt as usize;
                    }
                    ebpf::JEQ64_IMM
                    | ebpf::JEQ32_IMM
                    | ebpf::JNE64_IMM
                    | ebpf::JNE32_IMM
                    | ebpf::JGT64_IMM
                    | ebpf::JGT32_IMM
                    | ebpf::JSGT64_IMM
                    | ebpf::JSGT32_IMM
                    | ebpf::JSLE64_IMM
                    | ebpf::JSLE32_IMM
                    | ebpf::JLT64_IMM
                    | ebpf::JLT32_IMM
                    | ebpf::JLE64_IMM
                    | ebpf::JLE32_IMM
                    | ebpf::JEQ64_REG
                    | ebpf::JEQ32_REG
                    | ebpf::JNE64_REG
                    | ebpf::JNE32_REG
                    | ebpf::JLT64_REG
                    | ebpf::JLT32_REG
                    | ebpf::JSLE64_REG
                    | ebpf::JSLE32_REG
                        if branch_decision.is_taken() =>
                    {
                        pc_iter = jtgt as usize;
                    }
                    ebpf::CALL_IMM => {
                        // CALL_IMM: imm is a Murmur3 hash of either a syscall name or
                        // (for an internal call) the target PC. Resolve it as an
                        // internal call; if that misses, distinguish a syscall hash
                        // from a genuinely unresolved function so the diagnostic (and
                        // the coverage bucket) names the real gap.
                        let imm = ins.imm as u32;
                        pc_iter =
                            resolve_call_target_logical(ctx, analysis, ins).ok_or_else(|| {
                                match classify_call_imm(imm) {
                                    CallImmClassification::ModeledSyscall(name) => {
                                        let name = String::from_utf8_lossy(name);
                                        LiftError::new(
                                            DiagnosticKind::SyscallUntraced,
                                            format!(
                                        "qedlift: modeled syscall `{}` (imm 0x{:x}) reached at \
                                         pc {} in a no-trace static walk; provide a --trace to \
                                         dispatch it.",
                                        name, imm, pc_iter),
                                        )
                                    }
                                    CallImmClassification::UnmodeledSyscall(name) => {
                                        let name = String::from_utf8_lossy(name);
                                        LiftError::new(
                                            DiagnosticKind::SyscallUnmodeled,
                                            format!(
                                        "qedlift: unmodeled syscall `{}` (imm 0x{:x}) at pc {}; \
                                         add it to the SYSCALLS table to lift callers.",
                                        name, imm, pc_iter),
                                        )
                                    }
                                    CallImmClassification::Unknown => LiftError::new(
                                        DiagnosticKind::CallUnresolved,
                                        format!(
                                "qedlift: unresolved internal call at pc {} (imm 0x{:x}): not a \
                                 known syscall and no registry entry; extend the resolver.",
                                pc_iter, imm),
                                    ),
                                }
                            })?;
                    }
                    _ => {
                        pc_iter += 1;
                    }
                }
            }
        }

        // Blob tail-splits requested: record and re-walk.
        if !state.new_blob_splits.is_empty() {
            merge_blob_splits(&mut blob_splits, state.new_blob_splits.drain(..));
            continue;
        }
        // Demotion requested: merge new spans into hot set and re-walk (this pass discarded).
        if !state.new_hot.is_empty() {
            merge_hot_regions(&mut hot_regions, state.new_hot.drain(..));
            continue;
        }
        // H8 FAIL CLOSED: overlapping atom footprints make precondition's sepConj unsatisfiable (vacuous).
        if !state.overlap_errors.is_empty() {
            return Err(LiftError::new(
                DiagnosticKind::ByteAliasing,
                format!(
                    "qedlift: refusing to emit a vacuous lift — overlapping atom \
             footprints would make the precondition's sepConj \
             unsatisfiable. The walker does not yet alias these at byte \
             granularity (soundness-audit H8, \
             docs/QEDLIFT_ALIASING_DESIGN.md):\n  - {}",
                    state.overlap_errors.join("\n  - ")
                ),
            ));
        }
        return Ok(WalkResult {
            state,
            spec_calls,
            block_pcs,
            exit_pc,
            fault_terminal,
        });
    }
}
