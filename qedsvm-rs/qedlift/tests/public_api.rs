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
