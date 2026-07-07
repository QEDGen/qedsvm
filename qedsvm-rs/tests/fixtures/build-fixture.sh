#!/usr/bin/env bash
# Rebuild a fixture's deployed `.so` AND an unstripped `.debug` sidecar
# carrying DWARF, for the PC->function symbolication layer (qed-analysis).
#
# The deployed `.so` is byte-identical to a plain release build: adding
# `-C debuginfo=2 -C strip=none` only populates separate .debug_* / symtab
# sections and does not change `.text` codegen. cargo-build-sbf still emits
# a stripped artifact under target/deploy/, while the unstripped twin under
# target/sbpf-solana-solana/release/ carries the debug info. We ship the
# stripped one as `<name>.so` (unchanged -> decode pins + lifted proofs are
# untouched) and the unstripped one as `<name>.debug` (seashell convention).
#
# Usage:  ./build-fixture.sh <name>        # <name>_src/ must exist
set -euo pipefail

name="${1:?usage: build-fixture.sh <name>  (expects <name>_src/)}"
here="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.local/share/solana/install/active_release/bin:$PATH"

cd "$here/${name}_src"
RUSTFLAGS="-C debuginfo=2 -C strip=none" cargo-build-sbf

stripped="$(ls target/deploy/*.so | head -1)"
unstripped="$(ls target/sbpf-solana-solana/release/*.so | head -1)"

# Safety gate: never overwrite a committed `.so` whose bytes moved. A drifted
# build would silently break the kernel-checked decode pins (`*.pcs`) and the
# `Generated.*Lifted` proofs that hash `.text`.
if [ -f "$here/${name}.so" ] && ! cmp -s "$stripped" "$here/${name}.so"; then
  echo "ERROR: fresh ${name}.so differs from the committed one (toolchain drift?);" >&2
  echo "       refusing to overwrite -- this would break decode pins / lifted proofs." >&2
  exit 1
fi

cp "$stripped"   "$here/${name}.so"
cp "$unstripped" "$here/${name}.debug"
echo "wrote ${name}.so (stripped, unchanged) + ${name}.debug (DWARF sidecar)"
