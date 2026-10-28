#!/usr/bin/env bash
# Differential run: Firedancer's fd_vm (unmodified, bare-metal rv64 on QEMU),
# agave's interpreter (solana-sbpf, native) and qedsvm, on Firedancer's
# instruction vectors, hand-written seeds and a CU-boundary sweep of both.
# Fails on any disagreement not in allow.txt.
#
#   tools/fdvm-diff/run.sh [--no-fdvm]
#
# Env: FD   a Firedancer checkout at $FD_COMMIT (cloned sparse into $WORK if unset)
#      WORK scratch directory (default: build/fdvm-diff)
#      FUZZ_SEED, FUZZ_COUNT  the random batch (default: seed 1, 500 programs)
# --no-fdvm skips QEMU: qedsvm against agave and the vector expectations.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
FD_COMMIT=f8041cef3a30c6ba8f49e2c92cd1503230134e22
WORK=${WORK:-$root/build/fdvm-diff}
fdvm=1; [[ ${1:-} == --no-fdvm ]] && fdvm=0
mkdir -p "$WORK"
py() { python3 -I "$@"; }

if [[ -z ${FD:-} ]]; then
  FD=$WORK/firedancer
  if [[ ! -d $FD/.git ]]; then
    git clone -q --filter=blob:none --no-checkout https://github.com/firedancer-io/firedancer "$FD"
    git -C "$FD" sparse-checkout set --no-cone /src/
    git -C "$FD" checkout -q "$FD_COMMIT"
  fi
fi
[[ $(git -C "$FD" rev-parse HEAD) == "$FD_COMMIT" ]] || { echo "FD is not at $FD_COMMIT" >&2; exit 2; }
vec=$FD/src/flamenco/vm/instr_test

(cd "$root" && lake build qedcase >/dev/null)
qedcase=$root/.lake/build/bin/qedcase
(cd "$here/agave" && cargo build -q --release --locked)  # rust-toolchain.toml pins 1.97.1
agvcase=$here/agave/target/release/agvcase

# Base batches: the vectors (with expectations) and the seeds (without).
py "$here/instr2batch.py" "$vec"/v0/*.instr --version 0 -o "$WORK/v0.bin" --expect "$WORK/v0.expect.jsonl"
py "$here/instr2batch.py" "$vec"/v3/*.instr --version 3 -o "$WORK/v3.bin" --expect "$WORK/v3.expect.jsonl"
py "$here/synth.py" -o "$WORK/synth.bin" --expect "$WORK/synth.expect.jsonl"
py "$here/fuzz.py" --seed "${FUZZ_SEED:-1}" --count "${FUZZ_COUNT:-500}" \
  -o "$WORK/fuzz.bin" --expect "$WORK/fuzz.expect.jsonl"

# Sweeps: every completed base case at cost-1, cost, cost+1.
for b in v0 v3 synth fuzz; do
  "$qedcase" "$WORK/$b.bin" > "$WORK/$b.qed.txt"
  py "$here/sweep.py" "$WORK/$b.bin" "$WORK/$b.expect.jsonl" "$WORK/$b.qed.txt" \
    -o "$WORK/$b-sweep.bin" --expect "$WORK/$b-sweep.expect.jsonl"
done

status=0
for b in v0 v3 synth fuzz v0-sweep v3-sweep synth-sweep fuzz-sweep; do
  # Base batches already ran above (the sweep needs their costs).
  [[ $b == *-sweep ]] && "$qedcase" "$WORK/$b.bin" > "$WORK/$b.qed.txt"
  "$agvcase" "$WORK/$b.bin" > "$WORK/$b.agv.txt"
  args=(--qed "$WORK/$b.qed.txt" --agv "$WORK/$b.agv.txt")
  if (( fdvm )); then
    OUT=$WORK/out-$b FD=$FD "$here/harness/build.sh" "$WORK/$b.bin" --run \
      | grep '^FDVM' > "$WORK/$b.fdvm.txt"
    grep -q '^FDVM done' "$WORK/$b.fdvm.txt" || { echo "$b: fd_vm run did not finish" >&2; status=1; }
    args+=(--fd "$WORK/$b.fdvm.txt")
  fi
  echo "== $b"
  py "$here/diffcase.py" "$WORK/$b.expect.jsonl" "${args[@]}" --allow "$here/allow.txt" --strict \
    || status=1
done
exit $status
