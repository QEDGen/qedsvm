#!/usr/bin/env python3
"""Hand-written seed programs for the differential run, beyond Firedancer's
single-instruction vectors: the shapes behind #89 (CU budget boundary),
#90 (call depth) and #93 (syscall charge order).

Every seed is emitted at a generous budget; `sweep.py` then adds the
cost-1 / cost / cost+1 budgets. Seeds have no vector expectation
(`status: null`), so they are compared engine against engine only.

  synth.py -o synth.bin --expect synth.expect.jsonl"""
import argparse, json, os, struct, sys
sys.path.insert(0, os.path.dirname(__file__))
from caselib import insn, pack_case, pack_batch
from murmur import murmur3_32

SOL_LOG_64 = murmur3_32(b"sol_log_64_")   # the one syscall the rv64 harness models

def fn_key(slot):
    """V0 internal-call key: murmur3 of the target slot as a u64 (Elf.pcHash)."""
    return murmur3_32(struct.pack("<Q", slot))

def seeds():
    exit_ = insn(0x95)
    # sol_log_64_ (100 CU) then exit: the charge lands exactly on the budget edge.
    yield "log64", dict(text=insn(0x85, imm=SOL_LOG_64) + exit_)
    # Two log calls: the second charge crosses the edge after a successful first.
    yield "log64x2", dict(text=insn(0x85, imm=SOL_LOG_64) * 2 + exit_)
    # V0 self-recursion through the function registry: faults at depth 64.
    yield "depth_v0", dict(text=insn(0x85, imm=fn_key(0)) + exit_, calldests=(0,))
    # V3 self-recursion through a relative call (src=1, imm=-1).
    yield "depth_v3", dict(text=insn(0x85, src=1, imm=-1) + exit_, version=3)
    # Call to slot 2 that returns, 63 times deep then unwinds: depth just under the limit.
    body = insn(0xb7, dst=1, imm=62)                 # r1 = 62
    body += insn(0x85, imm=fn_key(3))                # call f
    body += exit_
    body += insn(0x15, dst=1, off=3)                 # f: if r1 == 0 goto ret
    body += insn(0x17, dst=1, imm=1)                 # r1 -= 1
    body += insn(0x85, imm=fn_key(3))                # call f
    body += insn(0x05, off=0)                        # ja +0
    body += exit_                                    # ret
    yield "depth63_v0", dict(text=body, calldests=(3,))
    # A straight-line ALU run long enough that the budget edge falls mid-program.
    yield "alu20", dict(text=insn(0x07, dst=0, imm=1) * 20 + exit_)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-o", required=True); ap.add_argument("--expect", required=True)
    a = ap.parse_args()
    cases, meta = [], []
    for name, s in seeds():
        cases.append(pack_case(s["text"], version=s.get("version", 0), budget=200_000,
                               calldests=s.get("calldests", ())))
        meta.append(dict(file="synth", line=name, status=None, exp=None, skip=None,
                         text=s["text"].hex()))
    open(a.o, "wb").write(pack_batch(cases))
    with open(a.expect, "w") as fh:
        for m in meta: fh.write(json.dumps(m) + "\n")
    print(f"{len(cases)} cases", file=sys.stderr)

if __name__ == "__main__":
    main()
