#!/usr/bin/env bash
#
# Run the 4 hand-written sBPF programs from
# `~/code/blueshift/asm` through `formal-svm-cli` — the Lean reference
# VM's CLI entrypoint. Each program is exercised with constructed
# inputs that hit both the success and (where applicable) failure
# branches.
#
# Usage:  ./demos/blueshift.sh
#
# Requires:
#   - formal-svm-cli built (lake build is automatic; cargo build --release
#     --bin formal-svm-cli for the Rust binary).
#   - Blueshift checkout at $BLUESHIFT (default: ~/code/blueshift).

set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
CLI="$REPO/formal-svm-rs/target/release/formal-svm-cli"
BLUESHIFT="${BLUESHIFT:-$HOME/code/blueshift}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

build_cli() {
  if [[ ! -x "$CLI" ]]; then
    echo ">> building formal-svm-cli..."
    (cd "$REPO/formal-svm-rs" && cargo build --release --bin formal-svm-cli)
  fi
}

run() {
  local label="$1" so="$2" input="$3"
  echo "── $label ──────────────────────────────────────"
  "$CLI" --elf "$so" --input "$input" | grep -v '^modified_input:\|^  hex:'
  echo
}

build_cli

# --- asm-hello: load string from .rodata, log it ---
: > "$TMP/empty.bin"
run "asm-hello (no input)" \
    "$BLUESHIFT/asm/asm-hello/deploy/asm-hello.so" \
    "$TMP/empty.bin"

# --- asm-memo: parse (count, len, data) from input, log data ---
python3 -c "
import struct
memo = b'hello blueshift'
out = struct.pack('<QQ', 0, len(memo)) + memo
import sys; sys.stdout.buffer.write(out)" > "$TMP/memo.bin"
run "asm-memo (memo='hello blueshift')" \
    "$BLUESHIFT/asm/asm-memo/deploy/asm-memo.so" \
    "$TMP/memo.bin"

# --- asm-slippage: token balance vs minimum, log on slippage ---
python3 -c "
import struct
buf = bytearray(0x2920)
struct.pack_into('<Q', buf, 0x00a0, 1000)  # avail balance
struct.pack_into('<Q', buf, 0x2918, 500)   # required min
import sys; sys.stdout.buffer.write(bytes(buf))" > "$TMP/slippage_ok.bin"
run "asm-slippage (avail=1000, min=500 → ok)" \
    "$BLUESHIFT/asm/asm-slippage/deploy/asm-slippage.so" \
    "$TMP/slippage_ok.bin"

python3 -c "
import struct
buf = bytearray(0x2920)
struct.pack_into('<Q', buf, 0x00a0, 100)   # avail balance
struct.pack_into('<Q', buf, 0x2918, 500)   # required min (insufficient)
import sys; sys.stdout.buffer.write(bytes(buf))" > "$TMP/slippage_fail.bin"
run "asm-slippage (avail=100,  min=500 → slippage)" \
    "$BLUESHIFT/asm/asm-slippage/deploy/asm-slippage.so" \
    "$TMP/slippage_fail.bin"

# --- asm-timeout: clock slot vs target slot ---
python3 -c "
import struct
buf = bytearray(0x28a0)
struct.pack_into('<Q', buf, 0x0060, 50)    # current slot
struct.pack_into('<Q', buf, 0x2898, 100)   # target slot (still in window)
import sys; sys.stdout.buffer.write(bytes(buf))" > "$TMP/timeout_ok.bin"
run "asm-timeout (current=50,  target=100 → in window)" \
    "$BLUESHIFT/asm/asm-timeout/deploy/asm-timeout.so" \
    "$TMP/timeout_ok.bin"

python3 -c "
import struct
buf = bytearray(0x28a0)
struct.pack_into('<Q', buf, 0x0060, 100)   # current slot
struct.pack_into('<Q', buf, 0x2898, 50)    # target slot (already past it)
import sys; sys.stdout.buffer.write(bytes(buf))" > "$TMP/timeout_late.bin"
run "asm-timeout (current=100, target=50  → timed out)" \
    "$BLUESHIFT/asm/asm-timeout/deploy/asm-timeout.so" \
    "$TMP/timeout_late.bin"

echo "Done — 4 programs, 6 input scenarios, all branches exercised."
