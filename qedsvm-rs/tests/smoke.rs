//! Smoke test: `run_buffer` on `helloElf` (RunnerDemo Demo 8) must return `Halted(42)`.

use qedsvm::{run_buffer, ExitOutcome};

const HELLO_ELF: &[u8] = include_bytes!("fixtures/hello.elf"); // 289B ELF: `mov64 r0, 42; exit` = SVM.SBPF.RunnerDemo.helloElf

#[test]
fn hello_elf_runs_through_lean_to_exit_42() {
    let result = run_buffer(HELLO_ELF, &[], 200_000).expect("ELF should decode and run");
    assert_eq!(result.outcome, ExitOutcome::Halted(42));
    assert!(
        result.modified_input.is_empty(),
        "no input given → empty output region"
    );
    assert!(result.logs.is_empty(), "program emits no logs");
    assert!(result.return_data.is_empty(), "program sets no return data");
}

#[test]
fn hello_elf_length_matches_lean_fixture() {
    assert_eq!(
        HELLO_ELF.len(),
        289,
        "must match SVM.SBPF.RunnerDemo.helloElf"
    );
}

#[test]
fn input_buffer_round_trips_unmodified_when_program_doesnt_touch_it() {
    let input = b"hello qedsvm"; // program never touches input region; must come back byte-identical
    let result = run_buffer(HELLO_ELF, input, 200_000).expect("ELF runs");
    assert_eq!(result.outcome, ExitOutcome::Halted(42));
    assert_eq!(result.modified_input, input);
}
