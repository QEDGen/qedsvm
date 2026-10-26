#!/usr/bin/env bash
# Same-build fixture pairs; no shared rustup override mutation.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
tools_version=v1.57
compiler="$HOME/.cache/solana/$tools_version/platform-tools/rust/bin/rustc"
if [[ ! -x "$compiler" ]]; then
  echo "Missing cached $tools_version compiler: $compiler" >&2
  echo "Install it with cargo-build-sbf --install-only --tools-version $tools_version" >&2
  exit 1
fi
build_root="$(mktemp -d "${TMPDIR:-/tmp}/qedsvm-debug-concepts.XXXXXX")"
for mode in full limited v3; do
  level=2
  suffix=""
  arch=v0
  triple=sbpf-solana-solana
  if [[ "$mode" == limited ]]; then level=1; suffix="_limited"; fi
  if [[ "$mode" == v3 ]]; then arch=v3; suffix="_v3"; triple=sbpfv3-solana-solana; fi
  RUSTC="$compiler" RUSTFLAGS="" CARGO_PROFILE_RELEASE_DEBUG="$level" \
    CARGO_TARGET_DIR="$build_root/$mode" cargo-build-sbf \
    --tools-version "$tools_version" --arch "$arch" --offline --no-rustup-override \
    --manifest-path "$here/debug_concepts_src/Cargo.toml"
  deployed="$build_root/$mode/deploy/qedsvm_debug_concepts.so"
  debug="$build_root/$mode/$triple/release/qedsvm_debug_concepts.so"
  cargo run --quiet --manifest-path "$repo/qedsvm-rs/Cargo.toml" \
    -p qed-analysis --bin qed-concept-map -- "$deployed" "$debug" \
    > "$build_root/debug_concepts${suffix}.json"
  cp "$deployed" "$build_root/debug_concepts${suffix}.so"
  cp "$debug" "$build_root/debug_concepts${suffix}.debug"
done
# Check all bytes before replacing any fixture, including debug identity pins.
for name in debug_concepts.so debug_concepts.debug debug_concepts_limited.so debug_concepts_limited.debug debug_concepts_v3.so debug_concepts_v3.debug; do
  if [[ -f "$here/$name" ]] && ! cmp -s "$here/$name" "$build_root/$name"; then
    echo "Refusing fixture drift: $name (new artifacts retained at $build_root)" >&2
    exit 1
  fi
done
for name in debug_concepts.so debug_concepts.debug debug_concepts_limited.so debug_concepts_limited.debug debug_concepts_v3.so debug_concepts_v3.debug; do
  cp "$build_root/$name" "$here/$name"
done
echo "Verified fixture pairs; build outputs and concept maps retained at $build_root"
