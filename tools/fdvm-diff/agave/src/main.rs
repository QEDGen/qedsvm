//! Run a batch of fd_vm-harness cases (format: ../caselib.py) through agave's
//! sBPF interpreter (`solana-sbpf`, verifier + interpreter, no JIT) and print
//! one outcome line per case, for `diffcase.py`.
//!
//!   agvcase <batch.bin>
//!
//! Setup mirrors `harness/fdvm_main.c` and agave's `create_vm`: the program
//! image is the text (`Executable::new_from_text_bytes`), mapped read-only at
//! 0x1_0000_0000 (V0) or 0 (V3); stack, heap (`heap_max`) and one flat writable
//! input region; r1 = input, r2 = `r2_initial`, then the register overrides.
//! V0 functions are the case's calldests, keyed by the murmur3 of their slot.
//! The only syscall is a CU-only `sol_log_64_` (100 CU, r0 = 0), like the
//! harness's model. Stack frame gaps and aligned memory mapping follow agave:
//! on unless `virtual_address_space_adjustments` (feature bit 2) is set.
//!
//! Cases this setup cannot express (a program image that is not the text,
//! a non-zero text offset or entry point) print `harness_error`.

use solana_sbpf::{
    aligned_memory::AlignedMemory,
    declare_builtin_function, ebpf,
    elf::Executable,
    error::ProgramResult,
    interpreter::Interpreter,
    memory_region::{MemoryMapping, MemoryRegion},
    program::{BuiltinProgram, FunctionRegistry, SBPFVersion},
    verifier::RequisiteVerifier,
    vm::{CallFrame, Config, ContextObject, EbpfVm},
};
use std::{ptr::NonNull, sync::Arc};

const MAGIC: u64 = 0x0032_5441_4256_4446; // "FDVBAT2\0"
const HDR_WORDS: usize = 24;
const FEAT_VAS_ADJUSTMENTS: u64 = 4;
const LOG_64_UNITS: u64 = 100;

/// CU meter and memory mapping, as agave's `InvokeContext` provides them.
struct Ctx {
    remaining: u64,
    mapping: MemoryMapping,
}

impl ContextObject for Ctx {
    fn consume(&mut self, amount: u64) {
        self.remaining = self.remaining.saturating_sub(amount);
    }
    fn get_remaining(&self) -> u64 {
        self.remaining
    }
    fn active_mapping_ptr(&mut self) -> NonNull<MemoryMapping> {
        NonNull::from(&mut self.mapping)
    }
}

declare_builtin_function!(
    /// `sol_log_64_`, CU only: agave's `consume_checked`, then r0 = 0.
    SolLog64,
    fn rust(
        ctx: &mut Ctx,
        _a: u64,
        _b: u64,
        _c: u64,
        _d: u64,
        _e: u64,
    ) -> Result<u64, Box<dyn std::error::Error>> {
        if ctx.remaining < LOG_64_UNITS {
            ctx.remaining = 0;
            return Err("ComputationalBudgetExceeded".into());
        }
        ctx.remaining -= LOG_64_UNITS;
        Ok(0)
    }
);

fn u64_at(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}

fn pad8(n: usize) -> usize {
    n.div_ceil(8) * 8
}

fn fnv(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |h, &x| {
        (h ^ x as u64).wrapping_mul(0x0100_0000_01b3)
    })
}

/// Runs the case whose header starts at byte `h`; returns its outcome line.
fn run_case(b: &[u8], idx: u64, h: usize) -> String {
    let w = |i: usize| u64_at(b, h + 8 * i);
    let (ver, entry_pc, budget, heap_max) = (w(0), w(1), w(2), w(3) as usize);
    let (text_cnt, rodata_sz, input_sz, cd_cnt) =
        (w(4) as usize, w(5) as usize, w(6) as usize, w(7) as usize);
    let (r2, text_off, features, reg_mask) = (w(8), w(9), w(10), w(11));
    let text_at = h + 8 * HDR_WORDS;
    let text = &b[text_at..text_at + 8 * text_cnt];
    let rodata_at = text_at + 8 * text_cnt;
    let rodata = &b[rodata_at..rodata_at + rodata_sz];
    let input_at = rodata_at + pad8(rodata_sz);
    let mut input = b[input_at..input_at + input_sz].to_vec();
    let cd_at = input_at + pad8(input_sz);
    let calldests: Vec<u64> = (0..cd_cnt).map(|i| u64_at(b, cd_at + 8 * i)).collect();

    let pre = format!("AGV case={idx:#x}");
    if rodata != text || text_off != 0 || entry_pc != 0 {
        return format!("{pre} harness_error=0x1");
    }
    let version = if ver >= 3 { SBPFVersion::V3 } else { SBPFVersion::V0 };
    let vas_adj = features & FEAT_VAS_ADJUSTMENTS != 0;
    let config = Config {
        enable_stack_frame_gaps: !vas_adj,
        aligned_memory_mapping: !vas_adj,
        reject_broken_elfs: true,
        optimize_rodata: false,
        enabled_sbpf_versions: SBPFVersion::V0..=SBPFVersion::V3,
        ..Config::default()
    };
    let mut loader = BuiltinProgram::new_loader(config);
    loader.register_definition::<SolLog64>("sol_log_64_").unwrap();
    let loader = Arc::new(loader);

    let mut registry = FunctionRegistry::default();
    if version == SBPFVersion::V0 {
        for &pc in &calldests {
            let key = ebpf::hash_symbol_name(&(pc as usize).to_le_bytes());
            if registry.register_function(key, *b"", pc as usize).is_err() {
                return format!("{pre} validate=0x1");
            }
        }
    }
    let Ok(executable) =
        Executable::<Ctx>::new_from_text_bytes(text, loader.clone(), version, registry)
    else {
        return format!("{pre} validate=0x1");
    };
    if executable.verify::<RequisiteVerifier>().is_err() {
        return format!("{pre} validate=0x1");
    }

    let config = executable.get_config();
    let mut stack = AlignedMemory::<{ ebpf::HOST_ALIGN }>::zero_filled(config.stack_size());
    let stack_len = stack.len();
    let mut heap = AlignedMemory::<{ ebpf::HOST_ALIGN }>::zero_filled(heap_max);
    let gap = if version.stack_frame_gaps() && config.enable_stack_frame_gaps {
        config.stack_frame_size as u64
    } else {
        0
    };
    let regions = vec![
        executable.get_ro_region(),
        MemoryRegion::new_gapped(&mut stack, ebpf::MM_STACK_START, gap),
        MemoryRegion::new(&mut heap, ebpf::MM_HEAP_START),
        MemoryRegion::new(input.as_mut_slice() as *mut [u8], ebpf::MM_INPUT_START),
    ];
    // SAFETY: stack, heap and input outlive the mapping (all dropped at the end
    // of this function, after the run).
    let mapping = match unsafe { MemoryMapping::new(regions, config, version) } {
        Ok(m) => m,
        Err(_) => return format!("{pre} harness_error=0x2"),
    };
    let mut ctx = Ctx { remaining: budget, mapping };

    let mut vm = EbpfVm::new(loader, version, &mut ctx, stack_len);
    vm.registers[1] = ebpf::MM_INPUT_START;
    vm.registers[2] = r2;
    for i in 0..11 {
        if reg_mask & (1 << i) != 0 {
            vm.registers[i] = w(12 + i);
        }
    }
    // `EbpfVm::execute_program`'s interpreted path, inlined: it returns only
    // r0, and the comparison needs every register after the run.
    let mut frames = vec![CallFrame::default(); config.max_call_depth];
    vm.registers[11] = executable.get_entrypoint_instruction_offset() as u64;
    vm.previous_instruction_meter = budget;
    vm.due_insn_count = 0;
    vm.program_result = ProgramResult::Ok(0);
    let registers = vm.registers;
    let mut interp = Interpreter::new(&mut vm, &executable, registers, &mut frames);
    while interp.step() {}
    let regs = interp.reg;
    let due = vm.due_insn_count;
    let result = std::mem::replace(&mut vm.program_result, ProgramResult::Ok(0));
    drop(vm);
    ctx.consume(due);
    let cu_used = budget - ctx.remaining;

    let (err, outcome) = match result {
        ProgramResult::Ok(r0) => (0, format!("exit:{r0:#018x}")),
        ProgramResult::Err(e) => {
            let kind = format!("{e:?}");
            let kind: String = kind.split(['(', ' ', '{']).next().unwrap_or("").into();
            (1, format!("fault:{kind}"))
        }
    };
    let regs: Vec<String> = (0..11).map(|i| format!("r{i}={:#018x}", regs[i])).collect();
    format!(
        "{pre} validate=0x0 err={err:#x} outcome={outcome} {} cu_used={cu_used:#018x} input_fnv={:#018x}",
        regs.join(" "),
        fnv(&input)
    )
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: agvcase <batch.bin>");
    let b = std::fs::read(path).expect("read batch");
    assert_eq!(u64_at(&b, 0), MAGIC, "bad batch magic");
    let mut off = 16;
    for i in 0..u64_at(&b, 8) {
        let len_words = u64_at(&b, off) as usize;
        println!("{}", run_case(&b, i, off + 8));
        off += 8 + 8 * len_words;
    }
}
