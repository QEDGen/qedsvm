#!/usr/bin/env python3
"""Convert Firedancer's text instruction vectors (src/flamenco/vm/instr_test/
*/*.instr) into a harness batch plus a JSONL of the vectors' expected results.

A faithful port of the parser in firedancer test_vm_instr.c: `input=`,
`region_boundary=`, op/dst/src/off/imm and r0..r11 are STICKY across vectors
(never reset at `$`); at `:` the expected registers start as a copy of the
input registers. Program = [insn, (lddw hi word), exit], rodata = text,
cu 100, heap 0, no calldests, all feature flags 0 (as test_vm_instr runs).

Vectors with region_boundary (fragmented input) are emitted with skip=reason,
since qedsvm models one flat input region."""
import argparse, json, re, sys
sys.path.insert(0, __import__("os").path.dirname(__file__))
from caselib import insn, pack_case, pack_batch

TOK = re.compile(r"\s*(#[^\n]*|\$|:|[A-Za-z_][A-Za-z0-9_]*|=|[0-9a-fA-F]+)")

def parse(text):
    st = dict(input=b"", rb=[], op=0, dst=0, src=0, off=0, imm=0, reg=[0] * 12)
    out, cur, mode, line_of = [], None, "in", None
    pos, line = 0, 1
    def finish():
        if cur is not None:
            out.append(cur)
    toks = []
    for m in TOK.finditer(text):
        toks.append((m.group(1), text.count("\n", 0, m.start(1)) + 1))
    i = 0
    eff = None
    def emit():
        out.append(dict(line=line_of, input=st["input"], rb=list(st["rb"]),
                        op=st["op"], dst=st["dst"], src=st["src"], off=st["off"],
                        imm=st["imm"], reg=list(st["reg"]), **eff))
    while i < len(toks):
        t, ln = toks[i]; i += 1
        if t.startswith("#"):
            continue
        if t == "$":
            if mode == "as": emit()
            mode, line_of = "in", ln
            continue
        if t == ":":
            mode = "as"; eff = dict(status="ok", force_exec=0, exp=list(st["reg"]))
            continue
        def val():
            nonlocal i
            if toks[i][0] == "=": i += 1
            v = toks[i][0]; i += 1
            return v
        if t == "input":
            st["input"] = bytes.fromhex(val()); st["rb"] = []
        elif t == "region_boundary":
            st["rb"].append(int(val(), 16))
        elif t in ("op", "dst", "src", "off", "imm"):
            st[t] = int(val(), 16)
        elif t == "ok":  eff["status"] = "ok"
        elif t == "err": eff["status"] = "err"
        elif t == "vfy": eff.update(status="vfy", force_exec=1)
        elif t == "vfyub": eff.update(status="vfy", force_exec=0)
        elif re.fullmatch(r"r\d+", t):
            r = int(t[1:]); v = int(val(), 16)
            (eff["exp"] if mode == "as" else st["reg"])[r] = v
        else:
            raise SystemExit(f"unexpected token {t!r} at line {ln}")
    if mode == "as": emit()
    return out

def program(v):
    text = insn(v["op"], v["dst"], v["src"], v["off"] - (1 << 16) * (v["off"] >> 15), v["imm"])
    if v["op"] == 0x18:
        text += insn(0, 0, 0, 0, v["imm"] >> 32)
    return text + insn(0x95)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+"); ap.add_argument("--version", type=int, required=True)
    ap.add_argument("-o", required=True); ap.add_argument("--expect", required=True)
    a = ap.parse_args()
    cases, meta = [], []
    for f in a.files:
        for v in parse(open(f).read()):
            text = program(v)
            regs = {i: x for i, x in enumerate(v["reg"])}
            cases.append(pack_case(text, version=a.version, budget=100, heap_max=0,
                                   input_=v["input"], regs=regs))
            meta.append(dict(file=f.split("/")[-1], line=v["line"], status=v["status"],
                             exp=v["exp"], skip="region_boundary" if v["rb"] else None,
                             text=text.hex()))
    open(a.o, "wb").write(pack_batch(cases))
    with open(a.expect, "w") as fh:
        for m in meta: fh.write(json.dumps(m) + "\n")
    print(f"{len(cases)} cases", file=sys.stderr)

if __name__ == "__main__":
    main()
