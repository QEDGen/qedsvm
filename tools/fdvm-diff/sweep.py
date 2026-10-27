#!/usr/bin/env python3
"""CU-boundary sweep: re-emit every case that ran to completion at budgets
cost-1, cost and cost+1, where cost is the CU it used. Off-by-one budget
checks (#89) and charge-order bugs (#93) only show at these edges.

  sweep.py base.bin base.expect.jsonl base.qed.txt -o sweep.bin --expect sweep.expect.jsonl

`base.qed.txt` is qedsvm's run of the base batch and supplies each cost. The
sweep cases carry no expectation (`status: null`), so they are compared
engine against engine only: a wrong cost in qedsvm moves the sweep, and the
fd_vm comparison then reports it."""
import argparse, json, re, struct, sys

LINE = re.compile(r"(\w+)=(\S+)")
BUDGET_WORD = 3          # u64 index of cu_budget, counting the len_words prefix

def cases(batch):
    _, cnt = struct.unpack_from("<QQ", batch)
    off = 16
    for _ in range(cnt):
        n = struct.unpack_from("<Q", batch, off)[0]
        yield bytearray(batch[off:off + 8 + 8 * n])
        off += 8 + 8 * n

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("batch"); ap.add_argument("expect"); ap.add_argument("qed")
    ap.add_argument("-o", required=True); ap.add_argument("--expect-out", "--expect", dest="out", required=True)
    a = ap.parse_args()
    batch = open(a.batch, "rb").read()
    exp = [json.loads(l) for l in open(a.expect)]
    qed = {}
    for l in open(a.qed):
        if l.startswith("QED") and "case=" in l:
            kv = dict(LINE.findall(l)); qed[int(kv["case"])] = kv
    out, meta = [], []
    for i, c in enumerate(cases(batch)):
        kv = qed.get(i)
        if exp[i]["skip"] or kv is None or "outcome" not in kv: continue
        if not (kv["outcome"].startswith("exit:") or kv["outcome"].startswith("fault:")): continue
        cost = int(kv["cu_consumed_raw"])
        for b in sorted({max(cost - 1, 1), cost, cost + 1}):
            struct.pack_into("<Q", c, 8 * BUDGET_WORD, b)
            out.append(bytes(c))
            meta.append(dict(file=exp[i]["file"], line=f"{exp[i]['line']}@cu{b}", status=None,
                             exp=None, skip=None, text=exp[i]["text"]))
    MAGIC = struct.unpack_from("<Q", batch)[0]
    open(a.o, "wb").write(struct.pack("<QQ", MAGIC, len(out)) + b"".join(out))
    with open(a.out, "w") as fh:
        for m in meta: fh.write(json.dumps(m) + "\n")
    print(f"{len(out)} cases", file=sys.stderr)

if __name__ == "__main__":
    main()
