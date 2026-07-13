//! qedrecover — recover Lean metadata for a compiled Solana program from a `.so` + Codama IDL + qedsvm overlay.

mod args;
mod emit;
mod idioms;
mod recover;

use std::path::Path;
use std::sync::Arc;

use sha2::Digest;
use solana_sbpf::{elf::Executable, program::BuiltinProgram, static_analysis::Analysis};

use qed_analysis::{layout::codama_number_size, NoopCtx, PcMap};

use crate::args::parse_args;
use crate::emit::{emit_lean, emit_qedmeta, EmitCtx};
use crate::recover::{
    collect_account_layouts, load_trace, recover_one, validate_account_layout_bindings, Idl,
    Overlay, OverlayIx, Recovery,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = parse_args().map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

    let overlay_text = std::fs::read_to_string(&args.overlay)?;
    let overlay: Overlay = toml::from_str(&overlay_text)?;
    let overlay_by_name: std::collections::BTreeMap<&str, &OverlayIx> = overlay
        .instructions
        .iter()
        .map(|ix| (ix.name.as_str(), ix))
        .collect();

    // IDL path is relative to the overlay file.
    let overlay_dir: &Path = args.overlay.parent().unwrap_or(Path::new("."));
    let idl_path = overlay_dir.join(&overlay.idl);
    let idl_text = std::fs::read_to_string(&idl_path)?;
    let idl: Idl = serde_json::from_str(&idl_text)?;
    let idl_value: serde_json::Value = serde_json::from_str(&idl_text)?;
    let account_layouts = collect_account_layouts(&idl_value);
    validate_account_layout_bindings(&overlay, &idl, &account_layouts)
        .map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

    let bytes = std::fs::read(&args.so)?;
    let loader = Arc::new(BuiltinProgram::new_mock());
    let executable: Executable<NoopCtx> = Executable::load(&bytes, loader)?;
    let analysis = Analysis::from_executable(&executable)?;
    // Shared with qedlift; pinned to agree with `analysis.instructions[].ptr` by issue #41 test.
    let pc_map = PcMap::from_insns(&analysis.instructions);

    println!("=== inputs ===");
    println!("  .so:     {}", args.so.display());
    println!("  overlay: {}", args.overlay.display());
    println!(
        "  idl:     {} (program {} @ {})",
        idl_path.display(),
        idl.program.name,
        idl.program.public_key
    );
    println!();

    println!("=== ELF analysis ===");
    println!("  entrypoint:   pc 0x{:x}", analysis.entrypoint);
    println!("  instructions: {}", analysis.instructions.len());
    println!("  basic blocks: {}", analysis.cfg_nodes.len());
    println!("  functions:    {}", analysis.functions.len());
    println!("  account layouts: {}", account_layouts.len());
    println!();

    // Overlay claims decorate the summary line but their absence does NOT skip recovery.
    println!("=== whole-program recovery ===");
    println!(
        "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  claim",
        "instruction", "disc", "dispatch (pc)", "armPc", "blks", "insns"
    );
    println!("  {}", "-".repeat(96));

    let mut total = 0usize;
    let mut recovered_ok = 0usize;
    let mut dispatch_miss = 0usize;
    let mut idl_unsupp = 0usize;

    for idl_ix in &idl.program.instructions {
        total += 1;
        let ov = overlay_by_name.get(idl_ix.name.as_str()).copied();
        let claim = match ov {
            Some(o) => {
                let refines = o.refines.as_deref().unwrap_or("?");
                let cu = o.cu_budget.map(|c| format!("CU={}", c)).unwrap_or_default();
                format!("{} {}", refines, cu).trim().to_string()
            }
            None => String::new(),
        };

        match recover_one(&analysis, &pc_map, idl_ix)? {
            Recovery::Unsupported => {
                idl_unsupp += 1;
                println!(
                    "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                    idl_ix.name, "—", "skip (idl)", "—", "—", "—", claim
                );
            }
            Recovery::DispatchMiss { disc } => {
                dispatch_miss += 1;
                println!(
                    "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                    idl_ix.name, disc.value, "not found", "—", "—", "—", claim
                );
            }
            Recovery::Arm(r) => {
                recovered_ok += 1;
                let dpc = format!("{}/{}", r.load_pc, r.jeq_pc);
                println!(
                    "  {:24}  {:>4}  {:>15}  {:>6}  {:>5}  {:>5}  {}",
                    idl_ix.name,
                    r.disc.value,
                    dpc,
                    r.arm_entry_logical,
                    r.arm_blocks.len(),
                    r.arm_insns,
                    claim
                );
            }
        }
    }

    println!("  {}", "-".repeat(96));
    println!(
        "  recovered: {}/{}   dispatch-miss: {}   idl-skipped: {}",
        recovered_ok, total, dispatch_miss, idl_unsupp
    );
    if recovered_ok < total {
        println!();
        println!("  legend:");
        println!(
            "    skip (idl)    — IDL shape qedrecover can't analyse yet (non-number arg, etc.)"
        );
        println!(
            "    not found     — IDL shape OK but no `ldx + jeq imm=<disc>` pair in the binary"
        );
    }
    println!();

    // Detailed pass for overlay-claimed instructions. Multi-instruction --output (directory) not yet implemented.
    let claimed: Vec<&OverlayIx> = overlay
        .instructions
        .iter()
        .filter(|o| o.refines.is_some())
        .collect();
    let trace_pcs = match args.trace.as_ref() {
        Some(p) => {
            if claimed.len() != 1 {
                return Err(format!(
                    "--trace is per-instruction but the overlay claims {} \
                     instructions; narrow the overlay to one",
                    claimed.len()
                )
                .into());
            }
            // Trace PCs are logical indices matching `CfgNode.instructions` ranges; no slot conversion.
            Some(load_trace(p)?)
        }
        None => None,
    };
    if !claimed.is_empty() {
        println!("=== detailed view (overlay-claimed) ===");
    }
    for ovix in claimed {
        let idl_ix = idl
            .program
            .instructions
            .iter()
            .find(|i| i.name == ovix.name)
            .ok_or_else(|| {
                format!(
                    "overlay names instruction `{}` but IDL has no such instruction",
                    ovix.name
                )
            })?;

        println!("  instruction: {}", ovix.name);
        println!("    refines:    {}", ovix.refines.as_deref().unwrap_or("—"));
        println!(
            "    cu_budget:  {}",
            ovix.cu_budget
                .map(|c| c.to_string())
                .unwrap_or_else(|| "—".to_string())
        );

        // Only numberTypeNode args have a fixed byte size; others abort (unsupported).
        let mut off: usize = 0;
        let mut disc_value: Option<i64> = None;
        println!("    ix_data:");
        for arg in &idl_ix.arguments {
            let kind = arg.ty.get("kind").and_then(|v| v.as_str()).unwrap_or("?");
            let format = arg
                .ty
                .get("format")
                .and_then(|v| v.as_str())
                .ok_or_else(|| {
                    format!(
                        "arg `{}` has non-number type ({}), unsupported in spike",
                        arg.name, kind
                    )
                })?;
            let sz = codama_number_size(format)
                .ok_or_else(|| format!("unsupported number format: {}", format))?;
            // `numberValueNode` carries the literal under "number"; other kinds are skipped.
            let default = arg
                .default_value
                .as_ref()
                .and_then(|d| d.get("number"))
                .and_then(|n| n.as_i64());
            if arg.name == "discriminator" {
                disc_value = default;
            }
            let default_str = default.map(|n| format!(" = {}", n)).unwrap_or_default();
            println!(
                "      [{:#x}..{:#x}] {} : {}{}",
                off,
                off + sz,
                arg.name,
                format,
                default_str
            );
            off += sz;
        }

        if let Some(v) = disc_value {
            println!(
                "    discriminator: u8 = {} (looks for `ldxb`/`ldxw` + `jeq imm = {}`)",
                v, v
            );
        }

        println!("    accounts:");
        for (i, acc) in idl_ix.accounts.iter().enumerate() {
            let signer = match &acc.is_signer {
                serde_json::Value::Bool(b) => {
                    if *b {
                        "signer"
                    } else {
                        "—"
                    }
                }
                serde_json::Value::String(s) if s == "either" => "signer?",
                _ => "—",
            };
            let writ = if acc.is_writable { "writable" } else { "ro" };
            let layout = ovix
                .account_layouts
                .get(&acc.name)
                .map(|l| format!(" layout={}", l))
                .unwrap_or_default();
            println!(
                "      [{}] {:14} {} {}{}",
                i, acc.name, writ, signer, layout
            );
        }

        match recover_one(&analysis, &pc_map, idl_ix)? {
            Recovery::Unsupported => {
                if disc_value.is_some() {
                    println!("    [skip recognition: unsupported discriminator shape]");
                } else {
                    println!("    [skip recognition: no numeric discriminator value]");
                }
            }
            Recovery::DispatchMiss { disc } => {
                println!(
                    "    dispatch:    NOT FOUND \
                          (no `{}` + `jeq imm={}` pair from entry)",
                    disc.format, disc.value
                );
            }
            Recovery::Arm(recovered) => {
                let ctx = EmitCtx {
                    overlay: &overlay,
                    ovix,
                    idl_ix,
                    recovered: &recovered,
                    trace: trace_pcs.as_ref(),
                };
                println!("    dispatch:");
                println!("      discriminator load:  pc {}", recovered.load_pc);
                println!(
                    "      jeq imm={}:           pc {}",
                    recovered.disc.value, recovered.jeq_pc
                );
                println!(
                    "      → arm entry:         pc {} (slot {})",
                    recovered.arm_entry_logical, recovered.arm_entry_slot
                );

                println!(
                    "      enclosing function: pc {} ({} blocks)",
                    recovered.enclosing_func_slot, recovered.func_block_count
                );

                println!("    arm slice (function-bounded):");
                println!(
                    "      basic blocks: {} (unconstrained: {})",
                    recovered.arm_blocks.len(),
                    recovered.unconstrained_blocks
                );
                println!("      instructions: {}", recovered.arm_insns);
                println!(
                    "      blocks with exits outside the function: {}",
                    recovered.exiting_block_count
                );

                {
                    let mut counts: std::collections::BTreeMap<&str, usize> =
                        std::collections::BTreeMap::new();
                    for idm in &recovered.idiom_tags {
                        *counts.entry(idm.name).or_default() += 1;
                    }
                    let rendered = counts
                        .iter()
                        .map(|(n, c)| format!("{} x{}", n, c))
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!(
                        "      idioms: {}",
                        if rendered.is_empty() {
                            "none".to_string()
                        } else {
                            rendered
                        }
                    );
                }

                let (n_zero, n_nonzero) =
                    recovered
                        .const_exits
                        .iter()
                        .fold((0usize, 0usize), |(z, nz), code| {
                            if code.exit_code == 0 {
                                (z + 1, nz)
                            } else {
                                (z, nz + 1)
                            }
                        });
                println!(
                    "      constant-exit blocks: {} success (code 0), {} error",
                    n_zero, n_nonzero
                );

                if let Some(t) = trace_pcs.as_ref() {
                    let happy = recovered
                        .arm_blocks
                        .iter()
                        .filter(|b| {
                            t.range(b.instructions.start..b.instructions.end)
                                .next()
                                .is_some()
                        })
                        .count();
                    println!(
                        "      happy-path blocks (on trace): {}/{} ({} traced PCs)",
                        happy,
                        recovered.arm_blocks.len(),
                        t.len()
                    );
                }

                if let Some(path) = &args.output {
                    let mut f = std::fs::File::create(path)?;
                    emit_lean(&mut f, &args, &pc_map, &ctx)?;
                    println!();
                    println!("=== emitted Lean metadata ===");
                    println!("  output: {}", path.display());
                } else {
                    println!();
                    println!("=== Lean metadata (stdout) ===");
                    let stdout = std::io::stdout();
                    let mut lock = stdout.lock();
                    emit_lean(&mut lock, &args, &pc_map, &ctx)?;
                }

                if let Some(meta_path) = &args.qedmeta_out {
                    let hex = |d: &[u8]| d.iter().map(|b| format!("{:02x}", b)).collect::<String>();
                    let so_sha256 = hex(&sha2::Sha256::digest(&bytes));
                    let idl_sha256 = hex(&sha2::Sha256::digest(idl_text.as_bytes()));
                    let mut f = std::fs::File::create(meta_path)?;
                    emit_qedmeta(
                        &mut f,
                        &idl,
                        &account_layouts,
                        &so_sha256,
                        &idl_sha256,
                        &ctx,
                    )?;
                    println!();
                    println!("=== emitted qedmeta sidecar ===");
                    println!("  output: {}", meta_path.display());
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use sha2::Digest as _;
    use solana_sbpf::{
        ebpf,
        elf::Executable,
        program::BuiltinProgram,
        static_analysis::{Analysis, CfgNode},
    };

    use qed_analysis::{NoopCtx, PcMap};

    use crate::emit::{emit_qedmeta, EmitCtx};
    use crate::idioms;
    use crate::recover::*;

    /// Pins slot-vs-logical space correctness on p_token. Computing the jump target from the
    /// vec index (not `insn.ptr`) was a real bug: transfer's arm returned as 309 instead of
    /// slot 336 / logical 304. Ground truth: `p_token_transfer.pcs` trace jumps 199 -> 304.
    #[test]
    fn transfer_arm_entry_spaces() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let (load_pc, jeq_pc, arm_entry_slot) =
            find_dispatch_arm(&analysis.instructions, 0, ebpf::LD_B_REG, 3)
                .expect("find transfer dispatch arm");

        assert_eq!((load_pc, jeq_pc), (198, 199), "dispatcher site moved");
        assert_eq!(arm_entry_slot, 336, "arm entry must be a slot PC");
        let pc_map = PcMap::from_insns(&analysis.instructions);
        assert_eq!(
            pc_map.slot_to_logical(arm_entry_slot),
            Some(304),
            "slot 336 must resolve to logical 304 (the PC the trace jumps to)"
        );

        let func_set = function_block_set(&analysis, arm_entry_slot);
        let arm_blocks = slice_cfg(&analysis, arm_entry_slot, Some(&func_set));
        let trace = load_trace(Path::new("../tests/fixtures/p_token_transfer.pcs"))
            .expect("load transfer trace");
        let happy = arm_blocks
            .iter()
            .filter(|b| {
                trace
                    .range(b.instructions.start..b.instructions.end)
                    .next()
                    .is_some()
            })
            .count();
        assert_eq!(
            happy, 27,
            "happy-path tagging drifted: expected 27 on-trace blocks, got {}",
            happy
        );

        // p_token transfer errors return computed r0 through calls; only the nine r0=0 success
        // funnels are constant exits. A nonzero hit = detector tagging computed codes (bug).
        let codes: Vec<u64> = arm_blocks
            .iter()
            .filter_map(|b| error_exit_code(&analysis, b))
            .collect();
        assert_eq!(codes.len(), 9, "constant-exit block count drifted");
        assert!(
            codes.iter().all(|&c| c == 0),
            "transfer arm has no constant nonzero exits; got {:?}",
            codes
        );
    }

    /// Issue #41: `PcMap` must agree with `analysis.instructions[].ptr` so qedrecover can use
    /// the shared converter instead of its former `binary_search`-over-`.ptr`. Full round-trip.
    #[test]
    fn pc_map_matches_analysis_ptrs() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let pc_map = PcMap::from_insns(&analysis.instructions);
        assert_eq!(
            pc_map.logical_len(),
            analysis.instructions.len(),
            "shared PcMap covers a different instruction count than analysis"
        );
        for (logical, insn) in analysis.instructions.iter().enumerate() {
            assert_eq!(
                pc_map.logical_to_slot(logical),
                Some(insn.ptr),
                "logical {} maps to a different slot than analysis .ptr",
                logical
            );
            assert_eq!(
                pc_map.slot_to_logical(insn.ptr),
                Some(logical),
                "slot {} (logical {}) failed to round-trip",
                insn.ptr,
                logical
            );
        }
    }

    /// Pins `error_exit_code` against two real p_token shapes: shape 1 `lddw r0,19<<32; exit`
    /// (dispatch-mismatch at logical 196) and shape 2 `lddw r0,10<<32; ja <bare exit>` (logical 124).
    #[test]
    fn entrypoint_error_landings_classify() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let block_containing = |logical: usize| -> &CfgNode {
            analysis
                .cfg_nodes
                .values()
                .find(|b| b.instructions.start <= logical && logical < b.instructions.end)
                .expect("block containing pc")
        };
        assert_eq!(
            error_exit_code(&analysis, block_containing(196)),
            Some(19u64 << 32),
            "dispatch-mismatch landing misclassified"
        );
        assert_eq!(
            error_exit_code(&analysis, block_containing(124)),
            Some(10u64 << 32),
            "prelude ja-landing misclassified"
        );
    }

    /// Idiom recogniser: pins debit/credit pair, dispatch load, and error-propagation seam on p_token.
    #[test]
    fn idioms_recognise_transfer_shapes() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");

        let (load_pc, _, arm_entry_slot) =
            find_dispatch_arm(&analysis.instructions, 0, ebpf::LD_B_REG, 3)
                .expect("find transfer dispatch arm");
        let func_set = function_block_set(&analysis, arm_entry_slot);
        let arm_blocks = slice_cfg(&analysis, arm_entry_slot, Some(&func_set));
        let tags = idioms::scan_arm(&analysis, &arm_blocks, Some((load_pc, 1)));

        assert!(tags
            .iter()
            .any(|i| i.pc == 198 && i.name == "read_discriminator"));
        assert!(
            tags.iter().any(|i| i.pc == 4673
                && i.name == "u64_field_decrement"
                && i.detail == "base=r5 off=72 amount=r8"),
            "transfer source debit not recognised"
        );
        assert!(
            tags.iter().any(|i| i.pc == 4676
                && i.name == "u64_field_increment"
                && i.detail == "base=r3 off=72 amount=r8"),
            "transfer dest credit not recognised"
        );
        // Concrete hit: pc 1286 `call 11385; mov64 r1,-1; jsgt r0,0`.
        assert!(
            tags.iter()
                .any(|i| i.name == "error_propagation_check"
                    && i.detail == "call_pc=1286 test_pc=1288"),
            "in-arm helper-result seam not recognised"
        );

        // Entrypoint seam: `call 12311; …; jne r0` at 59..63 — scan its block directly.
        let entry_block = analysis
            .cfg_nodes
            .values()
            .find(|b| b.instructions.start <= 59 && 59 < b.instructions.end)
            .expect("block containing the entrypoint call");
        let entry_tags = idioms::scan_arm(&analysis, &[entry_block], None);
        assert!(entry_tags.iter().any(|i| i.name == "error_propagation_check"
                && i.detail == "call_pc=59 test_pc=63"),
            "entrypoint error-propagation seam not recognised: {:?}",
            entry_tags.iter().map(|i| (i.pc, i.name)).collect::<Vec<_>>());
    }

    /// Issue #37/#41: pins the emitted transfer sidecar byte-identically (bless with
    /// QEDRECOVER_BLESS=1) and re-parses `recovered.arm_entry_pc` == 304 — closing the
    /// recover->lift handoff mechanically. Matches `transfer_arm_entry_spaces` + qedlift consumer.
    #[test]
    fn qedmeta_sidecar_emits_recovered_facts() {
        let bytes = std::fs::read("../tests/fixtures/p_token.so").expect("read p_token.so");
        let loader = Arc::new(BuiltinProgram::new_mock());
        let executable: Executable<NoopCtx> =
            Executable::load(&bytes, loader).expect("load p_token.so");
        let analysis = Analysis::from_executable(&executable).expect("analyse p_token.so");
        let pc_map = PcMap::from_insns(&analysis.instructions);

        let overlay: Overlay = toml::from_str(
            &std::fs::read_to_string("../tests/fixtures/p_token.qedoverlay.toml").unwrap(),
        )
        .unwrap();
        let ovix = overlay
            .instructions
            .iter()
            .find(|o| o.name == "transfer")
            .unwrap();
        let idl_text = std::fs::read_to_string("../tests/fixtures/spl_token.codama.json").unwrap();
        let idl: Idl = serde_json::from_str(&idl_text).unwrap();
        let idl_value: serde_json::Value = serde_json::from_str(&idl_text).unwrap();
        let account_layouts = collect_account_layouts(&idl_value);
        validate_account_layout_bindings(&overlay, &idl, &account_layouts)
            .expect("overlay account layout bindings");
        let idl_ix = idl
            .program
            .instructions
            .iter()
            .find(|i| i.name == "transfer")
            .unwrap();
        let recovered = match recover_one(&analysis, &pc_map, idl_ix).expect("recover transfer") {
            Recovery::Arm(r) => r,
            Recovery::Unsupported => panic!("transfer IDL should be recoverable"),
            Recovery::DispatchMiss { .. } => panic!("transfer dispatch arm should be found"),
        };
        let trace = load_trace(Path::new("../tests/fixtures/p_token_transfer.pcs")).expect("trace");

        let mut buf: Vec<u8> = Vec::new();
        let hex = |d: &[u8]| d.iter().map(|b| format!("{:02x}", b)).collect::<String>();
        let so_sha256 = hex(&sha2::Sha256::digest(&bytes));
        let idl_sha256 = hex(&sha2::Sha256::digest(idl_text.as_bytes()));
        let ctx = EmitCtx {
            overlay: &overlay,
            ovix,
            idl_ix,
            recovered: &recovered,
            trace: Some(&trace),
        };
        emit_qedmeta(
            &mut buf,
            &idl,
            &account_layouts,
            &so_sha256,
            &idl_sha256,
            &ctx,
        )
        .expect("emit qedmeta");
        let emitted = String::from_utf8(buf).expect("utf8");

        let fixture = "../tests/fixtures/p_token.transfer.recovered.qedmeta.toml";
        if std::env::var("QEDRECOVER_BLESS").is_ok() {
            std::fs::write(fixture, &emitted).expect("write fixture");
        }
        assert_eq!(
            emitted,
            std::fs::read_to_string(fixture).expect("read fixture"),
            "emitted qedmeta drifted from the pinned fixture \
             (regenerate with QEDRECOVER_BLESS=1)"
        );

        // Verify the consumer contract: parses through the same shape qedlift's QedMeta uses.
        #[derive(serde::Deserialize)]
        struct Field {
            name: String,
            offset: usize,
            kind: String,
        }
        #[derive(serde::Deserialize)]
        struct Layout {
            name: String,
            size: usize,
            field: Vec<Field>,
        }
        #[derive(serde::Deserialize)]
        struct Acct {
            name: String,
            layout: Option<String>,
        }
        #[derive(serde::Deserialize)]
        struct Rec {
            arm_entry_pc: usize,
            dispatch_load_pc: usize,
            dispatch_jeq_pc: usize,
        }
        #[derive(serde::Deserialize)]
        struct Ix {
            account: Vec<Acct>,
            recovered: Rec,
        }
        #[derive(serde::Deserialize)]
        struct Meta {
            schema_version: u32,
            #[serde(default)]
            account_layout: Vec<Layout>,
            #[serde(rename = "instruction")]
            instructions: Vec<Ix>,
        }
        let meta: Meta = toml::from_str(&emitted).expect("emitted sidecar must parse");
        assert_eq!(meta.schema_version, 2, "emitted schema must be v2");
        let token = meta
            .account_layout
            .iter()
            .find(|layout| layout.name == "token")
            .expect("token account layout emitted");
        assert_eq!(token.size, 165, "token layout size");
        let amount = token
            .field
            .iter()
            .find(|field| field.name == "amount")
            .expect("token amount field emitted");
        assert_eq!((amount.offset, amount.kind.as_str()), (64, "u64"));
        let rec = &meta.instructions[0].recovered;
        let source = meta.instructions[0]
            .account
            .iter()
            .find(|account| account.name == "source")
            .expect("source account emitted");
        assert_eq!(source.layout.as_deref(), Some("token"));
        let destination = meta.instructions[0]
            .account
            .iter()
            .find(|account| account.name == "destination")
            .expect("destination account emitted");
        assert_eq!(destination.layout.as_deref(), Some("token"));
        assert_eq!(
            rec.arm_entry_pc, 304,
            "emitted arm entry must be logical 304"
        );
        assert_eq!((rec.dispatch_load_pc, rec.dispatch_jeq_pc), (198, 199));
    }
}
