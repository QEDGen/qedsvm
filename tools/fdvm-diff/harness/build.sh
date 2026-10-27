#!/usr/bin/env bash
# Build the bare-metal rv64 fd_vm harness for one case and (optionally) run it.
#   FD=<firedancer checkout> ./build.sh <case.bin> [--run]
# Toolchain: docker image qedsvm-rv64-newlib (gcc 14.2 riscv64-unknown-elf +
# newlib 4.5, Debian trixie pinned by digest; Dockerfile in ../docker/).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${FD:?set FD to a firedancer checkout}"
case_bin=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
out=${OUT:-$here/out}; mkdir -p "$out"; cp "$case_bin" "$out/case.bin"
# TARGET=qemu (default) adds the HTIF fromhost handshake; TARGET=sail omits it
# and shrinks the static case buffers (crt0 zeroing is slow on the Sail model).
TARGET=${TARGET:-qemu}
if [[ $TARGET == qemu ]]; then EXTRA='-DHTIF_HANDSHAKE'; else EXTRA='-DCASE_BUF_SZ=65536UL'; fi
# rv64im: no C (compressed decode) and no A, to keep the proof-side ISA surface small.
MARCH=${MARCH:-rv64im}
docker run --rm -v "$FD":/fd:ro -v "$here":/h:ro -v "$out":/out qedsvm-rv64-newlib bash -c "
set -e
CF='-std=gnu17 -O2 -march=$MARCH -mabi=lp64 -mcmodel=medany -ffunction-sections -fdata-sections -I/fd/src -idirafter /opt/newlib/riscv64-unknown-elf/include -Wno-unused-parameter $EXTRA'
cd /out
riscv64-unknown-elf-gcc \$CF -c /fd/src/flamenco/vm/fd_vm_interp.c -o fd_vm_interp.o
riscv64-unknown-elf-gcc \$CF -c /fd/src/flamenco/vm/fd_vm.c        -o fd_vm.o
riscv64-unknown-elf-gcc \$CF -c /h/fdvm_main.c -o fdvm_main.o
riscv64-unknown-elf-gcc \$CF -c /h/stubs.c     -o stubs.o
riscv64-unknown-elf-gcc \$CF -c /h/syscall_models.c -o syscall_models.o
riscv64-unknown-elf-gcc \$CF -c /h/htif.c      -o htif.o
riscv64-unknown-elf-gcc -march=$MARCH -mabi=lp64 -c /h/crt0.S -o crt0.o
riscv64-unknown-elf-gcc -march=$MARCH -mabi=lp64 -c /h/case.S -o case.o -Wa,-I/out
riscv64-unknown-elf-gcc -march=$MARCH -mabi=lp64 -nostartfiles -T /h/link.ld -Wl,--gc-sections \
  -o fdvm.elf crt0.o case.o fdvm_main.o fd_vm_interp.o fd_vm.o stubs.o syscall_models.o htif.o \
  -L/opt/newlib/riscv64-unknown-elf/lib -lc -lgcc
riscv64-unknown-elf-size fdvm.elf
"
if [[ "${2:-}" == "--run" && $TARGET == sail ]]; then
  : "${SAIL:?set SAIL to the lean_riscv_emulator binary}"
  "$SAIL" "$out/fdvm.elf"
elif [[ "${2:-}" == "--run" ]]; then
  docker run --rm -v "$out":/out qedsvm-rv64-newlib timeout 60 \
    qemu-system-riscv64 -machine spike -bios none -nographic -kernel /out/fdvm.elf
fi
