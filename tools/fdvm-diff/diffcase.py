#!/usr/bin/env python3
"""Compare outcome lines (FDVM from the rv64 harness, QED from qedcase, AGV
from agave's interpreter via agvcase) against each other and against the
vectors' expected results.

  diffcase.py expect.jsonl [--fd fd.txt] [--qed qed.txt] [--agv agv.txt]
              [--allow allow.txt] [--strict]

Outcome classes: vfy (rejected by the verifier), err (runtime fault or out of
CU), ok (+ registers r0..r10). Against the vector expectations only the class
and, for ok, the registers are compared (the vectors record nothing else).
Engine against engine (qed-vs-fd, qed-vs-agv, fd-vs-agv) also compares the CU
used and the input region's hash, on every executed case: CU is charged on
failure too. AGV lines use the FDVM keys.

Cases with `status: null` (synth.py, sweep.py) have no expectation and are
compared engine against engine only.

--strict exits 1 on any disagreement not covered by --allow. An allow file
lists `<file>:<line> <issue>` per line (`#` comments), naming the issue that
tracks each known disagreement."""
import argparse, json, re, collections, sys

LINE = re.compile(r"(\w+)=(\S+)")

def load(path, tag):
    out = {}
    for l in open(path):
        if not l.startswith(tag) or "case=" not in l: continue
        kv = dict(LINE.findall(l)); out[int(kv["case"], 0)] = kv
    return out

def h(x): return int(x, 0)

def cls_fd(kv, full=False):
    if "harness_error" in kv: return ("harness", h(kv["harness_error"]))
    if h(kv["validate"]) != 0: return ("vfy", None)
    extra = (h(kv["cu_used"]), kv["input_fnv"]) if full else ()
    if h(kv["err"]) != 0: return ("err", None) + extra
    return ("ok", [h(kv[f"r{i}"]) for i in range(11)]) + extra

def cls_qed(kv, full=False):
    if kv.get("decode") == "fail": return ("vfy", None)
    extra = (h(kv["cu_used"]), kv["input_fnv"]) if full else ()
    if not kv["outcome"].startswith("exit:"): return ("err", None) + extra
    return ("ok", [h(kv[f"r{i}"]) for i in range(11)]) + extra

def load_allow(path):
    allow = {}
    for l in open(path) if path else []:
        l = l.split("#", 1)[0].split()
        if l: allow[l[0]] = l[1] if len(l) > 1 else "?"
    return allow

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("expect")
    ap.add_argument("--fd"); ap.add_argument("--qed"); ap.add_argument("--agv")
    ap.add_argument("--allow")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--show", type=int, default=15)
    a = ap.parse_args()
    exp = [json.loads(l) for l in open(a.expect)]
    fd = load(a.fd, "FDVM") if a.fd else {}
    qd = load(a.qed, "QED") if a.qed else {}
    ag = load(a.agv, "AGV") if a.agv else {}
    allow = load_allow(a.allow)
    tally = collections.Counter(); shown = collections.Counter(); unexpected = 0
    for i, e in enumerate(exp):
        if e["skip"]: tally["skipped:" + e["skip"]] += 1; continue
        pairs = []
        if e["status"] is not None:
            want = (e["status"], e["exp"][:11] if e["status"] == "ok" else None)
            if a.fd: pairs.append(("fd-vs-expected", cls_fd(fd[i]) if i in fd else ("missing",), want))
            if a.qed: pairs.append(("qed-vs-expected", cls_qed(qd[i]) if i in qd else ("missing",), want))
            if a.agv: pairs.append(("agv-vs-expected", cls_fd(ag[i]) if i in ag else ("missing",), want))
        q = lambda: cls_qed(qd[i], True) if i in qd else ("missing",)
        f = lambda: cls_fd(fd[i], True) if i in fd else ("missing",)
        g = lambda: cls_fd(ag[i], True) if i in ag else ("missing",)
        if a.fd and a.qed: pairs.append(("qed-vs-fd", q(), f()))
        if a.agv and a.qed: pairs.append(("qed-vs-agv", q(), g()))
        if a.agv and a.fd: pairs.append(("fd-vs-agv", f(), g()))
        where = f"{e['file']}:{e['line']}"
        for name, got, ref in pairs:
            if got == ref: tally[name + ":agree"] += 1; continue
            key = f"{name}:{ref[0]}->{got[0]}"
            if where in allow:
                tally[f"{key} (allowed, {allow[where]})"] += 1; continue
            tally[key] += 1; unexpected += 1
            if shown[key] < a.show:
                shown[key] += 1
                print(f"[{key}] {where} text={e['text']} ref={ref} got={got}")
    print("\n".join(f"{k}: {v}" for k, v in sorted(tally.items())))
    if a.strict and unexpected:
        print(f"FAIL: {unexpected} unexpected disagreement(s)", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
