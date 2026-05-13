//! Validate that concurrent callers correctly serialize through the
//! global Lean runtime lock.
//!
//! Lean's runtime is single-threaded. `cargo test` runs tests in
//! parallel by default; without our `LEAN_LOCK` Mutex we'd see heap
//! corruption manifesting as random panics, segfaults, or wrong
//! outputs. This test spawns N threads each running M iterations of
//! `run_buffer` and asserts every call produces the canonical
//! `Halted(42)` result.

use std::sync::Arc;
use std::thread;

use formal_svm::{run_buffer, ExitOutcome};

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
    // Same shape, but with non-empty inputs of varying sizes so the
    // Lean allocator sees actual heap pressure. Hello ELF doesn't
    // read the buffer, so the input contents don't matter — what we
    // care about is that the alloc/dec_ref dance under contention
    // doesn't corrupt anything.
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
