//! Smoke test: drive `run_buffer` through Lean and assert we get the
//! same exit code Lean's own `native_decide` test in
//! `Svm/SBPF/RunnerDemo.lean` (Demo 8) asserts.
//!
//! The ELF is byte-for-byte the `helloElf` fixture from that demo:
//! a hand-assembled 289-byte ELF64 sBPF binary whose `.text` is
//! `mov64 r0, 42; exit`. If this returns `Halted(42)` the round trip
//! through Lean's runtime is sound.

use qedsvm::{run_buffer, ExitOutcome};

/// 289-byte ELF64 sBPF binary containing `mov64 r0, 42; exit`.
/// Identical to `Svm.SBPF.RunnerDemo.helloElf` (Demo 8). Lives as a
/// binary fixture so we don't have to keep transcribing it.
const HELLO_ELF: &[u8] = include_bytes!("fixtures/hello.elf");

#[test]
fn hello_elf_runs_through_lean_to_exit_42() {
    let result = run_buffer(HELLO_ELF, &[], 200_000)
        .expect("ELF should decode and run");
    assert_eq!(result.outcome, ExitOutcome::Halted(42));
    assert!(result.modified_input.is_empty(), "no input given → empty output region");
    assert!(result.logs.is_empty(), "program emits no logs");
    assert!(result.return_data.is_empty(), "program sets no return data");
}

#[test]
fn hello_elf_length_matches_lean_fixture() {
    assert_eq!(HELLO_ELF.len(), 289, "must match Svm.SBPF.RunnerDemo.helloElf");
}

#[test]
fn input_buffer_round_trips_unmodified_when_program_doesnt_touch_it() {
    // `mov64 r0, 42; exit` never reads or writes the input region,
    // so whatever we put there should come back byte-identical.
    let input = b"hello qedsvm";
    let result = run_buffer(HELLO_ELF, input, 200_000).expect("ELF runs");
    assert_eq!(result.outcome, ExitOutcome::Halted(42));
    assert_eq!(result.modified_input, input);
}
