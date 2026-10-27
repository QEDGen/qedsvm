# fd_vm differential harness

Runs Firedancer's sBPF interpreter, **unmodified** and compiled for bare-metal
RISC-V (rv64), next to qedsvm on the same post-load program images, and fails
on any disagreement. It found #89, #90, #91, #92 and #93, and the call to an
unknown syscall being charged 100 CU. Tracking issue: #96.

```sh
tools/fdvm-diff/run.sh            # fd_vm on QEMU vs qedsvm (needs docker)
tools/fdvm-diff/run.sh --no-fdvm  # qedsvm vs the vector expectations only
```

The first run clones Firedancer (sparse, pinned to `f8041ce`) into
`build/fdvm-diff/`. Pass `FD=<checkout>` to use an existing one at that commit.
Build the toolchain image once:

```sh
docker build -t qedsvm-rv64-newlib tools/fdvm-diff/docker
```

## What runs

| batch | source | compared |
|---|---|---|
| `v0`, `v3` | Firedancer's `src/flamenco/vm/instr_test/{v0,v3}/*.instr` | fd_vm, qedsvm and the vector expectations |
| `synth` | `synth.py`: syscall charge at the budget edge, call depth 64 (V0 and V3), deep call/return, ALU run | fd_vm vs qedsvm |
| `*-sweep` | `sweep.py`: every completed case above at budgets cost-1, cost and cost+1 | fd_vm vs qedsvm |

Against the vectors, the outcome class (verifier reject, runtime error, ok)
and the registers are compared. Engine against engine also compares CU used
and the input region's hash, on failures too, since a failed transaction
still pays for its CU. Frame counts and registers after a fault are not
compared: neither survives a failed instruction.

Known disagreements go in `allow.txt` with their tracking issue. It is empty.

## Pieces

| file | what |
|---|---|
| `harness/` | bare-metal rv64 driver around Firedancer's `fd_vm_interp.c` / `fd_vm.c`; `build.sh` compiles it in the docker image and runs it on QEMU |
| `docker/Dockerfile` | gcc 14.2 `riscv64-unknown-elf` + newlib 4.5 (built from Debian's source) + QEMU, Debian pinned by digest |
| `caselib.py` | the batch format shared by the harness and `QedCase.lean` |
| `instr2batch.py` | a port of Firedancer's `.instr` vector parser (`test_vm_instr.c`) |
| `synth.py`, `sweep.py` | seed programs and the CU-boundary sweep |
| `QedCase.lean` | the same batch through qedsvm (`lake build qedcase`) |
| `diffcase.py` | the three-way diff; `--strict` fails on anything not allow-listed |

The harness's syscalls are CU-only models (`harness/syscall_models.c`), and
only `sol_log_64_` is registered. One flat input region is mapped: vectors
with `region_boundary` are skipped. Loading the ELF is out of scope here:
both engines start from the same post-load image.

## Not yet

From #96: ELF fixtures through qedsvm's loader, a fuzzer, agave's
`solana-sbpf` as a third oracle, and a nightly run on the Lean Sail RV64
model (build with `TARGET=sail MARCH=rv64i`; the executable Sail model has
no M extension).
