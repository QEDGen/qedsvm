#!/usr/bin/env bash
# Clone + build solanalib's `sbpf-oracle` (SPIKE).
#
# solanalib pins Lean v4.31.0 and `require`s Mathlib, so this needs `elan`
# (fetches the toolchain on demand) and network access for the git deps.
# The SBPF layer itself is Mathlib-free, so `lake build sbpf-oracle` only
# compiles the SBPF + Oracle closure; Mathlib is still cloned to satisfy the
# dependency graph (large), but its modules are not compiled for this target.
set -euo pipefail

VENDOR="${1:-$(cd "$(dirname "$0")" && pwd)/vendor}"
REPO=https://github.com/solana-foundation/leanprover-solanalib
DIR="$VENDOR/leanprover-solanalib"

mkdir -p "$VENDOR"
if [ ! -d "$DIR/.git" ]; then
  echo ">> cloning $REPO"
  git clone --depth 1 "$REPO" "$DIR"
else
  echo ">> reusing $DIR"
fi

cd "$DIR"
echo ">> toolchain: $(cat lean-toolchain)"
echo ">> lake build sbpf-oracle (this fetches Mathlib + toolchain on first run)"
lake build sbpf-oracle
echo ">> built: $DIR/.lake/build/bin/sbpf-oracle"
