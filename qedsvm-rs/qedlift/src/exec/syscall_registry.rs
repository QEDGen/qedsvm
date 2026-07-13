use solana_sbpf::ebpf;

use crate::diagnostic::{DiagnosticKind, LiftError};
use crate::input::BinaryCtx;
use crate::spec_call::SpecCall;
use crate::state::SymState;
use crate::syscalls::{
    emit_sol_create_program_address, emit_sol_get_sysvar, emit_sol_log, emit_sol_memcmp,
    emit_sol_memcpy, emit_sol_memset, emit_sol_set_return_data, emit_sol_sha256,
};

/// True if the immediate is the hash of a syscall the lift emits an effect spec for.
pub(crate) fn imm_is_modeled_syscall(imm: u32) -> bool {
    syscall_model(imm).is_some_and(|m| m.modeled)
}

/// A typed-fault terminal syscall a happy-path walk can end on (Phase 7
/// sub-item 3). Both halt with `exitCode := ERR_ABORT` and `vmError := .abort`
/// (audit L1's typed channel); they differ only in the `Syscall` constructor
/// and the library terminal-fault spec the `*_fault_correct` corollary composes.
#[derive(Clone, Copy)]
pub(crate) enum AbortKind {
    /// `.call .abort` — unconditional abort (`Abort.execAbort`).
    Abort,
    /// `.call .sol_panic_` — panic (logs a message, same `.abort` fault).
    SolPanic,
    /// `.call .sol_invoke_signed` — CPI. The PROOF-facing semantics is the
    /// fail-closed `Cpi.exec` stub (audit C4/C5): it faults with
    /// `.unsupportedInstruction` rather than fabricate an effect-free
    /// invoke, so an invoke ends the walk like a terminal even though the
    /// RUNNER's trace continues past it (the real CPI is executed by
    /// `executeFnCpiWithFuel`). The lifted prefix ends AT the invoke — the
    /// envelope the caller hands the syscall is a claim about that
    /// prefix's post (`SVM.Solana.cpiEnvelope`).
    Invoke,
    /// `.call .sol_invoke_signed_c` — the C-ABI CPI, same fail-closed stub
    /// (envelope predicate: `SVM.Solana.cpiEnvelopeC`).
    InvokeC,
}

impl AbortKind {
    /// Resolve a relocated `call_imm` immediate (a Murmur3 syscall hash) to a
    /// fault terminal, or `None` if it is not abort/sol_panic_.
    pub(super) fn from_hash(imm: u32) -> Option<AbortKind> {
        syscall_model(imm).and_then(|m| m.abort)
    }
    /// The Lean `Syscall` constructor (CodeReq singleton + `step`/`hCu` term).
    pub(crate) fn ctor(self) -> &'static str {
        match self {
            AbortKind::Abort => ".abort",
            AbortKind::SolPanic => ".sol_panic_",
            AbortKind::Invoke => ".sol_invoke_signed",
            AbortKind::InvokeC => ".sol_invoke_signed_c",
        }
    }
    /// The typed `VmError` the terminal faults with.
    pub(crate) fn vm_error(self) -> &'static str {
        match self {
            AbortKind::Abort | AbortKind::SolPanic => ".abort",
            AbortKind::Invoke | AbortKind::InvokeC => ".unsupportedInstruction",
        }
    }
    /// The library terminal-fault spec the corollary composes with (both
    /// pre-parametric over the prefix post, faulting as `.abort`).
    pub(crate) fn faults_spec(self) -> &'static str {
        match self {
            AbortKind::Abort => "call_abort_faults_spec",
            AbortKind::SolPanic => "call_sol_panic_faults_spec",
            AbortKind::Invoke => "call_sol_invoke_signed_faults_spec",
            AbortKind::InvokeC => "call_sol_invoke_signed_c_faults_spec",
        }
    }
}

/// An out-of-bounds (H6) syscall fault terminal (Phase 7 sub-item 3, the
/// `.accessViolation` family). Unlike abort/panic, the fault is CONDITIONAL on
/// the syscall's input region being out of bounds, so the corollary carries a
/// region requirement `rr` over the region register (`region_reg`, e.g. r1) and
/// `region_size`. Detected only on a trace where the syscall does NOT return
/// (the OOB execution is stuck), and composed via the Mem-Mem
/// `cuTripleWithinMem_seq_fault` (combined `rr = prefixRR ∧ OOB`).
#[derive(Clone, Copy)]
pub(crate) struct OobSyscall {
    /// Lean `Syscall` constructor (CodeReq singleton).
    pub(crate) ctor: &'static str,
    /// The library OOB fault triple (`cuTripleFaultsWithinMem … .accessViolation`).
    pub(crate) faults_spec: &'static str,
    /// The register whose value addresses the guarded region (1 = r1).
    pub(crate) region_reg: u8,
    /// The guarded region length in bytes (e.g. 32 for the secp hash input).
    /// Ignored when `region_len_reg` is set.
    pub(crate) region_size: i64,
    /// When the region length is REGISTER-sized (e.g. `sol_set_return_data`'s
    /// `[r1, r1+r2)`), the length register. The faults spec then takes both
    /// values plus its literal side conditions (discharged `by decide`), and
    /// the post must carry the length register as the SECOND atom.
    pub(crate) region_len_reg: Option<u8>,
    /// `true` if the guard is a WRITE check (`containsWritable`, e.g. a sysvar
    /// output); `false` for a READ check (`containsRange`, e.g. the secp input).
    /// Must match the `rr` of the syscall's `faults_oob` triple.
    pub(crate) region_writable: bool,
}

impl OobSyscall {
    /// Resolve a syscall hash to its OOB fault descriptor, or `None`.
    pub(super) fn from_hash(imm: u32) -> Option<OobSyscall> {
        syscall_model(imm).and_then(|m| m.oob)
    }
}

/// A trace-mode running-effect emitter (`dispatch_traced_syscall` row): shapes
/// the syscall's pre/post atoms + spec-call preamble at the walked PC.
type EffectFn = fn(
    &mut SymState,
    &mut Vec<SpecCall>,
    &mut Vec<usize>,
    usize,
    &BinaryCtx,
) -> Result<(), LiftError>;

/// One row of the modeled-syscall table: everything qedlift knows about a
/// syscall hash. The four consumers (`imm_is_modeled_syscall`,
/// `dispatch_traced_syscall`, `AbortKind::from_hash`, `OobSyscall::from_hash`)
/// all derive from `SYSCALLS`, so adding a syscall is a one-row change.
struct SyscallModel {
    /// Symbol name (murmur3-hashed into the relocated `call_imm` imm).
    name: &'static [u8],
    /// In `imm_is_modeled_syscall`'s set: the lift emits an effect spec for
    /// it, forcing the decode-pins path + `sl_block_iter` proof body.
    modeled: bool,
    /// Running-effect emitter for a traced syscall returning to pc+1.
    effect: Option<EffectFn>,
    /// Typed unconditional fault terminal (abort/panic/CPI stub).
    abort: Option<AbortKind>,
    /// Conditional out-of-bounds fault descriptor (H6 `.accessViolation`).
    oob: Option<OobSyscall>,
}

impl SyscallModel {
    /// Row template: fill only the lookups the syscall participates in.
    const DEFAULT: SyscallModel = SyscallModel {
        name: b"",
        modeled: false,
        effect: None,
        abort: None,
        oob: None,
    };
}

/// The single source of truth for the modeled-syscall set.
static SYSCALLS: &[SyscallModel] = &[
    SyscallModel {
        name: b"sol_memset_",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| {
            emit_sol_memset(s, sc, bp, pc);
            Ok(())
        }),
        ..SyscallModel::DEFAULT
    },
    // H8 Phase C-2: faithful buffer-write (rent/offset 0/length 17; else fail-closed).
    SyscallModel {
        name: b"sol_get_sysvar",
        modeled: true,
        effect: Some(emit_sol_get_sysvar),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_log_",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| {
            emit_sol_log(s, sc, bp, pc);
            Ok(())
        }),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_memcpy_",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| {
            emit_sol_memcpy(s, sc, bp, pc, false);
            Ok(())
        }),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_memmove_",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| {
            emit_sol_memcpy(s, sc, bp, pc, true);
            Ok(())
        }),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_memcmp_",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| {
            emit_sol_memcmp(s, sc, bp, pc);
            Ok(())
        }),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_set_return_data",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| {
            emit_sol_set_return_data(s, sc, bp, pc);
            Ok(())
        }),
        oob: Some(OobSyscall {
            ctor: ".sol_set_return_data",
            faults_spec: "call_sol_set_return_data_faults_oob_spec",
            region_reg: 1,
            region_size: 0,
            region_len_reg: Some(2),
            region_writable: false,
        }),
        ..SyscallModel::DEFAULT
    },
    // H6: single-slice hash — descriptor cells consumed
    // from the program's stores, input/output introduced.
    SyscallModel {
        name: b"sol_sha256",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| emit_sol_sha256(s, sc, bp, pc)),
        oob: Some(OobSyscall {
            ctor: ".sol_sha256",
            faults_spec: "call_sol_sha256_faults_oob_spec",
            region_reg: 3,
            region_size: 32,
            region_len_reg: None,
            region_writable: true,
        }),
        ..SyscallModel::DEFAULT
    },
    // H6: single-seed PDA — descriptor from stores, seed +
    // program_id + output introduced; off-curve surfaced.
    SyscallModel {
        name: b"sol_create_program_address",
        modeled: true,
        effect: Some(|s, sc, bp, pc, _| emit_sol_create_program_address(s, sc, bp, pc)),
        oob: Some(OobSyscall {
            ctor: ".sol_create_program_address",
            faults_spec: "call_sol_create_program_address_faults_oob_spec",
            region_reg: 3,
            region_size: 32,
            region_len_reg: None,
            region_writable: false,
        }),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_invoke_signed_rust",
        modeled: true,
        abort: Some(AbortKind::Invoke),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_invoke_signed_c",
        modeled: true,
        abort: Some(AbortKind::InvokeC),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"abort",
        abort: Some(AbortKind::Abort),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_panic_",
        abort: Some(AbortKind::SolPanic),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_secp256k1_recover",
        oob: Some(OobSyscall {
            ctor: ".sol_secp256k1_recover",
            faults_spec: "call_sol_secp256k1_recover_faults_oob_spec",
            region_reg: 1,
            region_size: 32,
            region_len_reg: None,
            region_writable: false,
        }),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_get_clock_sysvar",
        oob: Some(OobSyscall {
            ctor: ".sol_get_clock_sysvar",
            faults_spec: "call_sol_get_clock_sysvar_faults_oob_spec",
            region_reg: 1,
            region_size: 40,
            region_len_reg: None,
            region_writable: true,
        }),
        ..SyscallModel::DEFAULT
    },
    SyscallModel {
        name: b"sol_get_rent_sysvar",
        oob: Some(OobSyscall {
            ctor: ".sol_get_rent_sysvar",
            faults_spec: "call_sol_get_rent_sysvar_faults_oob_spec",
            region_reg: 1,
            region_size: 17,
            region_len_reg: None,
            region_writable: true,
        }),
        ..SyscallModel::DEFAULT
    },
];

/// Look up a relocated `call_imm` immediate (murmur3 syscall hash) in the
/// modeled-syscall table.
fn syscall_model(imm: u32) -> Option<&'static SyscallModel> {
    SYSCALLS
        .iter()
        .find(|m| imm == ebpf::hash_symbol_name(m.name))
}

/// Every syscall name the runtime knows (modeled or not), for turning a bare
/// CALL_IMM hash into a readable diagnostic. Mirrors `SVM/SBPF/SyscallHash.lean`.
/// A CALL_IMM whose imm hashes to one of these is a syscall, NOT an internal
/// `call_local`, so it must not be reported as an unresolved function.
static SYSCALL_NAMES: &[&[u8]] = &[
    b"abort",
    b"sol_alloc_free_",
    b"sol_alt_bn128_compression",
    b"sol_alt_bn128_group_op",
    b"sol_big_mod_exp",
    b"sol_blake3",
    b"sol_create_program_address",
    b"sol_curve_group_op",
    b"sol_curve_multiscalar_mul",
    b"sol_curve_validate_point",
    b"sol_curve_pairing_map",
    b"sol_curve_decompress",
    b"sol_get_clock_sysvar",
    b"sol_get_epoch_rewards_sysvar",
    b"sol_get_epoch_schedule_sysvar",
    b"sol_get_epoch_stake",
    b"sol_get_fees_sysvar",
    b"sol_get_last_restart_slot",
    b"sol_get_processed_sibling_instruction",
    b"sol_get_rent_sysvar",
    b"sol_get_return_data",
    b"sol_get_stack_height",
    b"sol_get_sysvar",
    b"sol_invoke_signed_c",
    b"sol_invoke_signed_rust",
    b"sol_keccak256",
    b"sol_log_",
    b"sol_log_64_",
    b"sol_log_compute_units_",
    b"sol_log_data",
    b"sol_log_pubkey",
    b"sol_memcmp_",
    b"sol_memcpy_",
    b"sol_memmove_",
    b"sol_memset_",
    b"sol_panic_",
    b"sol_poseidon",
    b"sol_remaining_compute_units",
    b"sol_secp256k1_recover",
    b"sol_set_return_data",
    b"sol_sha256",
    b"sol_try_find_program_address",
];

/// If `imm` is a syscall hash, return its name. Used to diagnose a CALL_IMM the
/// walker could not otherwise resolve: a modeled syscall reached in a no-trace
/// static walk, or an unmodeled syscall, reads very differently from a genuine
/// unresolved internal call.
pub(super) fn known_syscall_name(imm: u32) -> Option<&'static [u8]> {
    SYSCALL_NAMES
        .iter()
        .copied()
        .find(|n| ebpf::hash_symbol_name(n) == imm)
}

#[derive(Debug, Eq, PartialEq)]
pub(super) enum CallImmClassification {
    ModeledSyscall(&'static [u8]),
    UnmodeledSyscall(&'static [u8]),
    Unknown,
}

pub(super) fn classify_call_imm(imm: u32) -> CallImmClassification {
    match known_syscall_name(imm) {
        Some(name) if syscall_model(imm).is_some_and(|model| model.modeled) => {
            CallImmClassification::ModeledSyscall(name)
        }
        Some(name) => CallImmClassification::UnmodeledSyscall(name),
        None => CallImmClassification::Unknown,
    }
}

/// Arithmetic-shift-right value semantics mirroring `arsh_render`'s Lean
/// let/if form: sign bit replicates into the top `shift` bits.
pub(super) fn arsh_value(x: u64, shift: u64, bits: u32) -> u64 {
    if bits == 64 {
        let s = (shift % 64) as u32;
        ((x as i64) >> s) as u64
    } else {
        let s = (shift % 32) as u32;
        ((((x as u32) as i32) >> s) as u32) as u64
    }
}

/// Dispatch a traced syscall to the running-effect emitter registered for its hash.
pub(super) fn dispatch_traced_syscall(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc_iter: usize,
    imm: u32,
    ctx: &BinaryCtx,
) -> Result<(), LiftError> {
    if let Some(effect) = syscall_model(imm).and_then(|m| m.effect) {
        return effect(state, spec_calls, block_pcs, pc_iter, ctx);
    }
    // NOTE: sol_invoke_signed_rust never reaches here — it is an
    // AbortKind::Invoke walk TERMINAL (the proof-facing CPI is the
    // fail-closed `Cpi.exec` stub, so no running spec can cross it).
    Err(LiftError::new(
        DiagnosticKind::SyscallUnmodeled,
        format!(
            "call_imm at pc {} is a syscall (trace returns to {} \
         without a frame push) with imm hash 0x{:08x}, but only \
         sol_memset_ / sol_memcpy_ / sol_memmove_ / sol_memcmp_ / \
         sol_get_sysvar / sol_log_ / sol_set_return_data are \
         modelled so far (sol_invoke_signed terminates the walk). \
         This arm needs a syscall-effect spec for that hash.",
            pc_iter,
            pc_iter + 1,
            imm
        ),
    ))
}
