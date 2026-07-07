#!/usr/bin/env bash
# Lift-coverage survey: run `qedlift --coverage` over a corpus and rank the
# fail-closed reasons across it. The measurement instrument for the lift
# frontier -- the empirical answer to "which walker/syscall gap is next".
#
# Green-pinned arms (p_token's traced paths) read ~100%; the signal is the
# untraced real programs, where genuine gaps surface. Buckets are defined in
# `classify_lift_failure` (src/bin/qedlift/driver.rs).
#
# Usage:  scripts/lift-coverage.sh          # curated corpus below
#         QEDLIFT=path/to/qedlift scripts/lift-coverage.sh
set -uo pipefail
cd "$(dirname "$0")/.."
BIN=${QEDLIFT:-target/debug/qedlift}
FIX=tests/fixtures

# Traced flagship (baseline) + representative untraced real / complex programs.
CORPUS=(
  p_token
  associated_token
  janus_pyth_price_resolver_devnet
  janus_slot_height_resolver_devnet
  libupstream_pinocchio_escrow
  cpi_caller
  cpi_increment_caller
  cpi_two_account_caller
  cpi_signed_pda_caller
  cpi_depth_2_outer
  cpi_envelope_caller
  curve_msm_probe
  curve_validate_probe
)

tmp=$(mktemp)
for so in "${CORPUS[@]}"; do
  [ -f "$FIX/$so.so" ] || { echo "coverage $so: (missing .so, skipped)"; continue; }
  timeout 180 "$BIN" --so "$FIX/$so.so" --coverage 2>/dev/null | tee -a "$tmp" \
    || echo "coverage $so: (timeout/crash)"
done

echo ""
echo "=== aggregate frontier: failures by bucket, most first ==="
# Bucket lines are "  <count>  <bucket>"; reason lines carry a colon. Tally.
grep -E '^[[:space:]]+[0-9]+[[:space:]]+[a-z-]+$' "$tmp" \
  | awk '{cnt[$2]+=$1} END {for (b in cnt) printf "%4d  %s\n", cnt[b], b}' \
  | sort -rn
rm -f "$tmp"
