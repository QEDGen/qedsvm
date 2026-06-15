//! Concurrent-caller safety: validates `LEAN_LOCK` Mutex serializes access to the single-threaded Lean runtime.
//! Without the lock, cargo test's parallel execution causes heap corruption (panics/segfaults/wrong outputs).

use std::sync::Arc;
use std::thread;

use qedsvm::{run_buffer, ExitOutcome};

const HELLO_ELF: &[u8] = include_bytes!("fixtures/hello.elf");

const THREADS: usize = 8;
const ITERS_PER_THREAD: usize = 50;

#[test]
fn concurrent_run_buffer_calls_serialize_correctly() {
    let elf: Arc<&'static [u8]> = Arc::new(HELLO_ELF);

    let mut handles = Vec::with_capacity(THREADS);
    for t in 0..THREADS {
        let elf = Arc::clone(&elf);
        handles.push(thread::spawn(move || {
            for i in 0..ITERS_PER_THREAD {
                let result = run_buffer(*elf, &[], 200_000)
                    .unwrap_or_else(|e| panic!("thread {t} iter {i}: decode failed: {e}"));
                assert_eq!(
                    result.outcome,
                    ExitOutcome::Halted(42),
                    "thread {t} iter {i}: unexpected outcome",
                );
                assert!(result.logs.is_empty());
                assert!(result.return_data.is_empty());
            }
        }));
    }

    for h in handles {
        h.join().expect("worker thread panicked");
    }
}

#[test]
fn varied_input_buffer_lengths_under_concurrency() {
    // Non-empty varying inputs create heap pressure; asserts alloc/dec_ref under contention doesn't corrupt.
    let mut handles = Vec::with_capacity(THREADS);
    for t in 0..THREADS {
        handles.push(thread::spawn(move || {
            for i in 0..ITERS_PER_THREAD {
                let size = ((t * 17) + (i * 31)) % 4096;
                let input: Vec<u8> = (0..size).map(|x| (x % 256) as u8).collect();
                let result = run_buffer(HELLO_ELF, &input, 200_000)
                    .unwrap_or_else(|e| panic!("t{t} i{i}: {e}"));
                assert_eq!(result.outcome, ExitOutcome::Halted(42));
                assert_eq!(result.modified_input, input,
                    "input region was perturbed under contention");
            }
        }));
    }
    for h in handles {
        h.join().expect("worker thread panicked");
    }
}
