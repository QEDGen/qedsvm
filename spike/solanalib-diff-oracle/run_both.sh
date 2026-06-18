#!/usr/bin/env bash
# Run both oracles on a corpus and diff (SPIKE).
#   run_both.sh corpus.txt
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
CORPUS="${1:-$HERE/corpus_core.txt}"

QEDSVM_EXE="$HERE/../../.lake/build/bin/qedsvm-oracle"
SOLANALIB_EXE="${SOLANALIB_EXE:-$HERE/vendor/leanprover-solanalib/.lake/build/bin/sbpf-oracle}"

[ -x "$QEDSVM_EXE" ] || { echo "missing $QEDSVM_EXE (run: lake build qedsvm-oracle)"; exit 2; }
[ -x "$SOLANALIB_EXE" ] || { echo "missing $SOLANALIB_EXE (run: ./build_solanalib.sh)"; exit 2; }

echo ">> qedsvm oracle"
"$QEDSVM_EXE"    < "$CORPUS" > "$HERE/qedsvm.out"
echo ">> solanalib oracle"
"$SOLANALIB_EXE" < "$CORPUS" > "$HERE/solanalib.out"
echo ">> diff"
python3 "$HERE/diff.py" "$CORPUS" "$HERE/qedsvm.out" "$HERE/solanalib.out"
