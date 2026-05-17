#!/usr/bin/env bash
#
# Run the doppler oracle program (https://github.com/blueshift-gg/doppler)
# through formal-svm's Lean reference VM. Exercises all three code paths
# of the program — including the two `lddw r0, N; exit` inline-asm
# fast paths embedded in `Admin::check` and `Oracle::check_and_update`.
#
# Usage:    ./examples/doppler.sh
#
# Requires: a built `doppler_program.so`. To build:
#   git clone https://github.com/blueshift-gg/doppler.git /tmp/doppler
#   # The bundled rustc rejects `#[no_mangle]` on the panic_handler item;
#   # delete that line from doppler/doppler/src/panic_handler.rs first
#   # (line 13 of the macro body), then:
#   cd /tmp/doppler/program && cargo-build-sbf
# Point DOPPLER_SO to the resulting .so, default: /tmp/doppler/target/deploy/

set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
CLI="$REPO/formal-svm-rs/target/release/formal-svm-cli"
DOPPLER_SO="${DOPPLER_SO:-/tmp/doppler/target/deploy/doppler_program.so}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

if [[ ! -f "$DOPPLER_SO" ]]; then
  echo "doppler_program.so not found at $DOPPLER_SO" >&2
  echo "build instructions: see the script header" >&2
  exit 1
fi

if [[ ! -x "$CLI" ]]; then
  echo ">> building formal-svm-cli..."
  (cd "$REPO/formal-svm-rs" && cargo build --release --bin formal-svm-cli)
fi

run() {
  local label="$1" input="$2"
  echo "── $label ──────────────────────────────────────"
  "$CLI" --elf "$DOPPLER_SO" --input "$input" | grep -v '^modified_input:\|^  hex:'
  echo
}

# === Scenario 1: happy path — admin OK + new_seq > current_seq ===
python3 -c "
import struct
ADMIN = bytes([0x08,0x9d,0xbe,0xc9,0x64,0x97,0xab,0xd0,0xdb,0x21,0x79,0x52,0x69,0xba,0xb9,0x4b,
               0xc8,0xb8,0x49,0xcc,0x05,0xaa,0x94,0x54,0xd0,0xa5,0xdc,0x76,0xec,0xcb,0x51,0xd1])
buf = bytearray(0x50f0)
struct.pack_into('<H', buf, 0x0008, 0x01ff)  # NO_DUP_SIGNER (signer + no-dup)
buf[0x0010:0x0010+32] = ADMIN
struct.pack_into('<Q', buf, 0x28c0, 100)     # current sequence
struct.pack_into('<Q', buf, 0x28c8, 1000)    # current payload (price=1000)
struct.pack_into('<Q', buf, 0x50e0, 101)     # new sequence (101 > 100 → update)
struct.pack_into('<Q', buf, 0x50e8, 1500)    # new payload (price=1500)
import sys; sys.stdout.buffer.write(bytes(buf))" > "$TMP/ok.bin"
run "admin OK + new_seq=101 > current=100 → update" "$TMP/ok.bin"

# === Scenario 2: bad admin header — hits `lddw r0, 1; exit` inline asm ===
python3 -c "
import struct
buf = bytearray(0x50f0)
struct.pack_into('<H', buf, 0x0008, 0xdead)  # WRONG header
import sys; sys.stdout.buffer.write(bytes(buf))" > "$TMP/bad_admin.bin"
run "bad admin header → Admin::check fast-exit (r0=1)" "$TMP/bad_admin.bin"

# === Scenario 3: stale oracle — hits `lddw r0, 2; exit` inline asm ===
python3 -c "
import struct
ADMIN = bytes([0x08,0x9d,0xbe,0xc9,0x64,0x97,0xab,0xd0,0xdb,0x21,0x79,0x52,0x69,0xba,0xb9,0x4b,
               0xc8,0xb8,0x49,0xcc,0x05,0xaa,0x94,0x54,0xd0,0xa5,0xdc,0x76,0xec,0xcb,0x51,0xd1])
buf = bytearray(0x50f0)
struct.pack_into('<H', buf, 0x0008, 0x01ff)
buf[0x0010:0x0010+32] = ADMIN
struct.pack_into('<Q', buf, 0x28c0, 100)     # current seq
struct.pack_into('<Q', buf, 0x50e0, 100)     # new seq = current → stale (not >)
import sys; sys.stdout.buffer.write(bytes(buf))" > "$TMP/stale.bin"
run "stale oracle (new_seq=100 ≤ current=100) → Oracle fast-exit (r0=2)" \
    "$TMP/stale.bin"

echo "Done — 3 scenarios, both inline-asm fast paths exercised."
