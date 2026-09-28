use std::path::Path;

use qedlift::{
    CpiCalleeContract, CpiSuffix, LiftOptions, Lifter, ProgramImage, RefinementOutcome,
    RefinementReason,
};

#[test]
fn lifts_traced_v3_callx_with_pinned_target() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_callx_path.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let trace = [0, 1, 4, 5, 2, 3];
    let result = lifter.lift(LiftOptions {
        trace: Some(&trace),
        ..LiftOptions::default()
    })?;
    assert!(result.lean.contains("callx_v3_spec"));
    assert!(result.lean.contains(".callx .r2"));
    assert!(result
        .lean
        .contains("resolveCallx rt (toU64 4294967336) = some 4"));
    assert!(result.lean.contains("_v3_callx_resolves"));
    assert_eq!(
        result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
        include_str!("../../../examples/lean/Generated/Sbpfv3CallxPathLifted.lean")
    );
    Ok(())
}

#[test]
fn rejects_v3_callx_trace_with_wrong_target() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_callx_path.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let wrong_trace = [0, 1, 2, 3];
    let error = lifter
        .lift(LiftOptions {
            trace: Some(&wrong_trace),
            ..LiftOptions::default()
        })
        .err()
        .expect("wrong indirect target must be rejected");
    assert_eq!(error.kind(), qedlift::DiagnosticKind::TraceInput);
    Ok(())
}

#[test]
fn lifts_v3_cpi_caller_with_callee_contract_bridge() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_cpi_caller.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let result = lifter.lift(LiftOptions::default())?;
    assert!(result.lean.contains("import SVM.SBPF.CpiBridge"));
    assert!(result
        .lean
        .contains("theorem Sbpfv3CpiCallerLifted_cpi_bridge"));
    assert!(result.lean.contains("Cpi.cuTripleWithinMem_cpi_bridge"));
    assert_eq!(
        result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiCallerLifted.lean")
    );
    Ok(())
}

#[test]
fn composes_v3_cpi_caller_paths_across_the_invoke() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_cpi_caller.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let (prefix, modules) = lifter.lift_cpi_paths(
        LiftOptions::default(),
        "Generated.Sbpfv3CpiCallerLifted",
        &CpiCalleeContract::MemoryPreserving,
        &[
            CpiSuffix {
                name: "Success",
                trace: &[35, 39, 40, 41],
            },
            CpiSuffix {
                name: "Rollback",
                trace: &[35, 36, 37, 38, 40, 41],
            },
        ],
    )?;
    let fix = |s: &str| s.replace("../tests/fixtures/", "tests/fixtures/");
    assert_eq!(
        fix(&prefix.lean),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiCallerLifted.lean")
    );
    assert_eq!(modules.len(), 2);
    assert_eq!(
        fix(&modules[0].lean),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiCallerLiftedSuccess.lean")
    );
    assert_eq!(
        fix(&modules[1].lean),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiCallerLiftedRollback.lean")
    );
    assert!(modules[0].lean.contains("(fun r => (r.code = toU64 0))"));
    assert!(modules[1].lean.contains("(fun r => (r.code ≠ toU64 0))"));
    Ok(())
}

#[test]
fn composes_v3_account_writing_cpi_paths() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_cpi_writer.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let (prefix, modules) = lifter.lift_cpi_paths(
        LiftOptions::default(),
        "Generated.Sbpfv3CpiWriterLifted",
        &CpiCalleeContract::WritesInputBytes(vec![96]),
        &[
            CpiSuffix {
                name: "Success",
                trace: &[47, 51, 52, 53, 54, 55, 56],
            },
            CpiSuffix {
                name: "Rollback",
                trace: &[47, 48, 49, 50, 55, 56],
            },
        ],
    )?;
    let fix = |s: &str| s.replace("../tests/fixtures/", "tests/fixtures/");
    assert_eq!(
        fix(&prefix.lean),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiWriterLifted.lean")
    );
    assert_eq!(
        fix(&modules[0].lean),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiWriterLiftedSuccess.lean")
    );
    assert_eq!(
        fix(&modules[1].lean),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiWriterLiftedRollback.lean")
    );
    // The suffix's read of the written byte is the committed value, and the
    // contract is the explicit write footprint.
    assert!(modules[0]
        .lean
        .contains("(hW : Cpi.writesOnly callee [effectiveAddr baseAddr 96])"));
    assert!(modules[0]
        .lean
        .contains("Cpi.committedByte r (effectiveAddr baseAddr 96) cpiFpOld0"));
    assert!(modules[0].lean.contains("SatWitness.sat_witness"));
    Ok(())
}

#[test]
fn rejects_duplicate_cpi_footprint_bytes() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_cpi_writer.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let error = lifter
        .lift_cpi_paths(
            LiftOptions::default(),
            "Generated.Sbpfv3CpiWriterLifted",
            &CpiCalleeContract::WritesInputBytes(vec![96, 96]),
            &[CpiSuffix {
                name: "Success",
                trace: &[47, 51, 52, 53, 54, 55, 56],
            }],
        )
        .err()
        .expect("duplicate footprint bytes must be rejected");
    assert_eq!(error.kind(), qedlift::DiagnosticKind::UnsupportedConstruct);
    Ok(())
}

#[test]
fn lifts_the_cpi_writer_callee() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_cpi_writer_callee.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let result = lifter.lift(LiftOptions {
        trace: Some(&[0, 1, 2, 3]),
        module_override: Some("Sbpfv3CpiWriterCalleeLifted".to_string()),
        ..LiftOptions::default()
    })?;
    assert_eq!(
        result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
        include_str!("../../../examples/lean/Generated/Sbpfv3CpiWriterCalleeLifted.lean")
    );
    Ok(())
}

#[test]
fn rejects_cpi_suffix_not_starting_after_invoke() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_cpi_caller.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let error = lifter
        .lift_cpi_paths(
            LiftOptions::default(),
            "Generated.Sbpfv3CpiCallerLifted",
            &CpiCalleeContract::MemoryPreserving,
            &[CpiSuffix {
                name: "Wrong",
                trace: &[36, 37, 38, 40, 41],
            }],
        )
        .err()
        .expect("suffix must start at invokePc + 1");
    assert_eq!(error.kind(), qedlift::DiagnosticKind::TraceInput);
    Ok(())
}

#[test]
fn v0_cpi_caller_emits_no_bridge() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/cpi_envelope_caller.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let result = lifter.lift(LiftOptions::default())?;
    assert!(!result.lean.contains("_cpi_bridge"));
    assert!(!result.lean.contains("SVM.SBPF.CpiBridge"));
    Ok(())
}

#[test]
fn lifts_v3_account_path_with_versioned_decode_pins() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_account_path.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let trace = [0, 1, 3, 5, 6, 7, 8, 9, 10, 4];
    let result = lifter.lift(LiftOptions {
        trace: Some(&trace),
        ..LiftOptions::default()
    })?;
    assert!(result.lean.contains("_v3_elf_text"));
    assert!(result.lean.contains("FnRegistry .v3"));
    assert!(result.lean.contains("jmp32_imm_spec .eq"));
    assert!(result.lean.contains("call_sol_log_64_spec"));
    assert_eq!(
        result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
        include_str!("../../../examples/lean/Generated/Sbpfv3AccountPathLifted.lean")
    );
    Ok(())
}

#[test]
fn lifts_toolchain_built_v3_account_path() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_compiled_account.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let trace = [11, 12, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 17];
    let result = lifter.lift(LiftOptions {
        trace: Some(&trace),
        ..LiftOptions::default()
    })?;
    assert!(result.lean.contains("_v3_elf_text"));
    assert!(result.lean.contains("jmp32_imm_spec .eq"));
    assert!(result.lean.contains("simp only [h_branch0, if_true]"));
    assert_eq!(
        result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
        include_str!("../../../examples/lean/Generated/Sbpfv3CompiledAccountLifted.lean")
    );
    Ok(())
}

#[test]
fn lifts_every_non_call_v3_form_on_one_path() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_isa_matrix.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let trace: Vec<usize> = (0..127).collect();
    let result = lifter.lift(LiftOptions {
        trace: Some(&trace),
        module_override: Some("Sbpfv3IsaMatrixLifted".to_string()),
        ..LiftOptions::default()
    })?;
    // All 44 conditional jumps carry jointly satisfiable path hypotheses.
    assert!(result.lean.contains("(h_branch43 :"));
    assert!(result.lean.contains("Branch-satisfiability witness"));
    assert!(result.lean.contains("jump32Holds .sle"));
    assert_eq!(
        result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
        include_str!("../../../examples/lean/Generated/Sbpfv3IsaMatrixLifted.lean")
    );
    Ok(())
}

#[test]
fn shares_complete_v3_elf_across_two_paths() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_compiled_account.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let update = [11, 12, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 17];
    let skip = [11, 12, 13, 14, 16, 17];
    for (name, trace) in [
        ("Sbpfv3SharedUpdate", update.as_slice()),
        ("Sbpfv3SharedSkip", skip.as_slice()),
    ] {
        let result = lifter.lift(LiftOptions {
            module_override: Some(name.to_string()),
            trace: Some(trace),
            shared_text: Some("Sbpfv3Shared"),
            ..LiftOptions::default()
        })?;
        assert!(result.lean.contains("import Generated.Sbpfv3SharedText"));
        assert!(result.lean.contains("Decode.decodeInsn Sbpfv3SharedText"));
        assert!(result.lean.contains(" .v3"));
        assert!(!result.lean.contains("def Sbpfv3SharedElf"));
        let (module, shared) = result.shared_text.expect("shared V3 module");
        assert_eq!(module, "Sbpfv3SharedText");
        assert!(shared.contains("Elf.loadV3 Sbpfv3SharedElf"));
        assert!(shared.contains("def Sbpfv3SharedElf : ByteArray"));
        assert!(shared.contains("def Sbpfv3SharedText : ByteArray"));
        assert!(shared.contains("def Sbpfv3SharedSlotMap"));
        assert!(shared.contains("def Sbpfv3SharedFnRegistry : List (Nat × Nat) := []"));
        let expected_path = if name == "Sbpfv3SharedUpdate" {
            include_str!("../../../examples/lean/Generated/Sbpfv3SharedUpdate.lean")
        } else {
            include_str!("../../../examples/lean/Generated/Sbpfv3SharedSkip.lean")
        };
        assert_eq!(
            result.lean.replace("../tests/fixtures/", "tests/fixtures/"),
            expected_path
        );
        assert_eq!(
            shared.replace("../tests/fixtures/", "tests/fixtures/"),
            include_str!("../../../examples/lean/Generated/Sbpfv3SharedText.lean")
        );
    }
    Ok(())
}

#[test]
fn unknown_v3_static_syscall_has_typed_diagnostic() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/sbpfv3_syscall_static.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let error = match lifter.lift(LiftOptions::default()) {
        Err(error) => error,
        Ok(_) => panic!("unknown V3 static syscall must fail closed"),
    };
    assert_eq!(error.kind(), qedlift::DiagnosticKind::SyscallUnmodeled);
    assert!(error.to_string().contains("V3 static syscall"));
    Ok(())
}

#[test]
fn lifts_a_program_without_cli_or_file_output() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/byte_increment.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;

    let result = lifter.lift(LiftOptions::default())?;

    assert_eq!(result.module_name, "ByteIncrementLifted");
    assert_eq!(result.insn_count, 5);
    assert_eq!(result.refinement_outcome, RefinementOutcome::NotRequested);
    assert!(result
        .lean
        .contains("theorem ByteIncrementLifted_lifted_spec"));
    Ok(())
}

#[test]
fn rejects_an_empty_programmatic_trace() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/byte_increment.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;

    let error = match lifter.lift(LiftOptions {
        trace: Some(&[]),
        ..LiftOptions::default()
    }) {
        Err(error) => error,
        Ok(_) => panic!("empty traces must fail closed"),
    };

    assert_eq!(error.kind(), qedlift::DiagnosticKind::TraceInput);
    assert_eq!(
        error.to_string(),
        "qedlift: trace must contain at least one logical PC"
    );
    Ok(())
}

#[test]
fn refuses_unbound_parameter_refinement() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/vault_deposit.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let mut desc = qed_artifacts::load_descriptor(Path::new(
        "../tests/fixtures/vault_deposit.descriptor.json",
    ))?;
    let idl: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(
        "../tests/fixtures/vault.codama.json",
    )?)?;
    desc.op = qed_artifacts::DescriptorOp::AddParam {
        add_param: "not_the_argument".into(),
    };
    let result = lifter.lift(LiftOptions {
        descriptor: Some(&desc),
        idl: Some(&idl),
        ..LiftOptions::default()
    })?;
    assert!(
        result.refinement.is_none(),
        "an arbitrary runtime read must not satisfy a named argument obligation"
    );
    assert!(matches!(
        result.refinement_outcome,
        RefinementOutcome::Rejected {
            reason: RefinementReason::InvalidParameterBinding,
            ..
        }
    ));
    Ok(())
}

#[test]
fn binds_parameter_to_serialized_instruction_data() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/vault_deposit.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let desc = qed_artifacts::load_descriptor(Path::new(
        "../tests/fixtures/vault_deposit.descriptor.json",
    ))?;
    let idl: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(
        "../tests/fixtures/vault.codama.json",
    )?)?;
    let result = lifter.lift(LiftOptions {
        descriptor: Some(&desc),
        idl: Some(&idl),
        ..LiftOptions::default()
    })?;
    assert_eq!(result.refinement_outcome, RefinementOutcome::Emitted);
    let (_, lean) = result
        .refinement
        .expect("bound parameter must emit refinement");
    // Independently calculated aligned input: total at 96+32, amount at
    // 8 + 88 + align8(41+10240) + 8 + 8 = 10400.
    assert!(lean.contains("effectiveAddr baseAddr 10400 ↦U64"));
    assert!(lean.contains("u64FieldAt 128"));
    assert_eq!(
        serde_json::to_value(result.refinement_outcome)?,
        serde_json::json!({"status":"emitted"})
    );
    Ok(())
}

#[test]
fn rejects_wrong_argument_address_and_account_binding() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/vault_deposit.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let idl: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(
        "../tests/fixtures/vault.codama.json",
    )?)?;
    let original: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(
        "../tests/fixtures/vault_deposit.descriptor.json",
    )?)?;
    for (lengths, index, reason) in [
        (vec![49], 0, RefinementReason::ParameterMismatch),
        (vec![41], 1, RefinementReason::InvalidParameterBinding),
        (
            vec![usize::MAX],
            0,
            RefinementReason::InvalidParameterBinding,
        ),
    ] {
        let mut json = original.clone();
        json["input_layout"] =
            serde_json::json!({"account_data_lengths": lengths, "account_index": index});
        let desc = serde_json::from_value(json)?;
        let result = lifter.lift(LiftOptions {
            descriptor: Some(&desc),
            idl: Some(&idl),
            ..LiftOptions::default()
        })?;
        assert!(result.refinement.is_none());
        assert!(
            matches!(result.refinement_outcome, RefinementOutcome::Rejected { reason: actual, .. } if actual == reason)
        );
    }
    // Same argument name and type, but bytes actually read the preceding arg.
    let mut shifted = idl.clone();
    shifted["program"]["instructions"][0]["arguments"].as_array_mut().unwrap().insert(0,
        serde_json::json!({"name":"other", "type":{"kind":"numberTypeNode", "format":"u64", "endian":"le"}}));
    let desc = serde_json::from_value(original)?;
    let result = lifter.lift(LiftOptions {
        descriptor: Some(&desc),
        idl: Some(&shifted),
        ..LiftOptions::default()
    })?;
    assert!(matches!(
        result.refinement_outcome,
        RefinementOutcome::Rejected {
            reason: RefinementReason::ParameterMismatch,
            ..
        }
    ));
    Ok(())
}

#[test]
fn legacy_parameter_descriptor_has_an_explicit_unsupported_verdict(
) -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/vault_deposit.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let mut desc = qed_artifacts::load_descriptor(Path::new(
        "../tests/fixtures/vault_deposit.descriptor.json",
    ))?;
    desc.schema_version = 2;
    let idl: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(
        "../tests/fixtures/vault.codama.json",
    )?)?;
    let result = lifter.lift(LiftOptions {
        descriptor: Some(&desc),
        idl: Some(&idl),
        ..LiftOptions::default()
    })?;
    assert!(result.refinement.is_none());
    assert!(matches!(
        result.refinement_outcome,
        RefinementOutcome::Unsupported {
            reason: RefinementReason::MissingParameterBinding,
            ..
        }
    ));
    Ok(())
}

#[test]
fn cli_fails_when_requested_refinement_is_unavailable() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_qedlift"))
        .args([
            "--so",
            "../tests/fixtures/vault_deposit.so",
            "--descriptor",
            "../tests/fixtures/vault_deposit.descriptor.json",
        ])
        .output()
        .expect("run qedlift without required IDL");
    assert!(!output.status.success());
    assert!(
        output.stdout.is_empty(),
        "failure must not stream a misleading partial artifact"
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    let report = stderr
        .lines()
        .find_map(|line| line.strip_prefix("refinement outcome: "))
        .expect("structured outcome");
    let report: serde_json::Value = serde_json::from_str(report).unwrap();
    assert_ne!(report["status"], "emitted");
}

#[test]
fn distinguishes_missing_bindings_from_conflicting_obligations(
) -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/vault_deposit.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let idl: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(
        "../tests/fixtures/vault.codama.json",
    )?)?;
    for missing in ["handler", "input_layout"] {
        let mut desc: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(
            "../tests/fixtures/vault_deposit.descriptor.json",
        )?)?;
        desc.as_object_mut().unwrap().remove(missing);
        let desc = serde_json::from_value(desc)?;
        let result = lifter.lift(LiftOptions {
            descriptor: Some(&desc),
            idl: Some(&idl),
            ..LiftOptions::default()
        })?;
        assert!(matches!(
            result.refinement_outcome,
            RefinementOutcome::Unsupported {
                reason: RefinementReason::MissingParameterBinding,
                ..
            }
        ));
        assert!(result.refinement.is_none());
    }
    let path = Path::new("../tests/fixtures/counter.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;
    let mut desc =
        qed_artifacts::load_descriptor(Path::new("../tests/fixtures/counter.descriptor.json"))?;
    desc.op = qed_artifacts::DescriptorOp::AddConst { add_const: 7 };
    let result = lifter.lift(LiftOptions {
        descriptor: Some(&desc),
        ..LiftOptions::default()
    })?;
    assert!(matches!(
        result.refinement_outcome,
        RefinementOutcome::Rejected {
            reason: RefinementReason::MutationMismatch,
            ..
        }
    ));
    assert!(result.refinement.is_none());
    Ok(())
}
