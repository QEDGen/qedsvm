use std::path::Path;

use qedlift::{LiftOptions, Lifter, ProgramImage};

#[test]
fn lifts_a_program_without_cli_or_file_output() -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new("../tests/fixtures/byte_increment.so");
    let program = ProgramImage::load(path)?;
    let lifter = Lifter::new(path, &program)?;

    let result = lifter.lift(LiftOptions::default())?;

    assert_eq!(result.module_name, "ByteIncrementLifted");
    assert_eq!(result.insn_count, 5);
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
