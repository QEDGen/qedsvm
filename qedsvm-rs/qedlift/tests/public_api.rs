use std::path::Path;

use qedlift::{LiftOptions, Lifter, ProgramImage, RefinementOutcome, RefinementReason};

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
