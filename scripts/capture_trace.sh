#!/usr/bin/env bash
# Capture a happy-path PC trace (.pcs) from the Lean reference VM.
#
# Usage:
#   scripts/capture_trace.sh <diff_mollusk_test_name> <out.pcs>
#
# Example:
#   scripts/capture_trace.sh p_token_transfer_matches_mollusk \
#     qedsvm-rs/tests/fixtures/p_token_transfer.pcs
#
# Runs the named diff_mollusk test with QEDSVM_TRACE_OUT set; the
# interpreter's traceStep hook (SVM/SBPF/Runner.lean -> lean-bridge)
# writes one decimal logical PC per line. No source edits, no rebuild,
# no stderr post-processing (this replaced the old flip-TRACE_STEPS
# ritual).
#
# Caveats:
# - One test per invocation (--exact). Two traced executions in one
#   process would interleave into a single file.
# - The trace covers every execution the test performs in the qedsvm
#   engine, in order. For a test that runs exactly one instruction
#   (the diff_mollusk convention) that is the happy path of that
#   instruction. CPI callee steps are recorded too: the callee runs
#   on the same interpreter.
# - PCs are logical instruction indices (the same numbering qedlift
#   and qedrecover use), one per executed CU plus the terminal exit.
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: $0 <diff_mollusk_test_name> <out.pcs>" >&2
  exit 1
fi

TEST_NAME="$1"
OUT="$2"
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

OUT_ABS="$(cd "$(dirname "$OUT")" 2>/dev/null && pwd)/$(basename "$OUT")" || {
  echo "error: output directory for $OUT does not exist" >&2
  exit 1
}

QEDSVM_TRACE_OUT="$OUT_ABS" cargo test --release \
  --manifest-path "$REPO_ROOT/qedsvm-rs/Cargo.toml" \
  --features diff-mollusk --test diff_mollusk \
  "$TEST_NAME" -- --exact

if [ ! -s "$OUT_ABS" ]; then
  echo "error: no trace written — did the test name match exactly?" >&2
  exit 1
fi

echo "wrote $(wc -l < "$OUT_ABS" | tr -d ' ') PCs to $OUT"
