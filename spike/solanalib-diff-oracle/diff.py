#!/usr/bin/env python3
"""
Diff harness for the solanalib differential oracle (SPIKE).

Aligns the corpus with the two oracle output files line-for-line and buckets
each (qedsvm, solanalib) outcome pair. The buckets that matter:

  DIVERGE-VALUE    both `ok`, different return value      <- REAL semantic bug
  DIVERGE-OUTCOME  one `ok`, the other not-ok             <- REAL, unless it is
                   a qedsvm `reject` (verifier-fold) which is reported as a
                   separate "qedsvm-stricter" sub-bucket, not a hard divergence.

Usage:
  diff.py corpus.txt qedsvm.out solanalib.out
"""
import sys
from collections import Counter


def classify_pair(corpus_line, q, s):
    qok = q.startswith("ok ")
    sok = s.startswith("ok ")
    if qok and sok:
        return ("AGREE-OK", None) if q == s else ("DIVERGE-VALUE", (q, s))
    if not qok and not sok:
        # both not-ok; q may be `reject`/`fault`, s may be `fault`/`error`
        if q == "reject":
            return ("AGREE-NOTOK (qedsvm-reject)", None)
        return ("AGREE-FAULT", None)
    # exactly one is ok
    if qok and not sok:
        return ("DIVERGE q-ok/s-notok", (q, s))
    # s ok, q not ok
    if q == "reject":
        return ("STRICTER q-reject/s-ok", (q, s))
    return ("DIVERGE q-notok/s-ok", (q, s))


def main():
    if len(sys.argv) != 4:
        print(__doc__)
        sys.exit(2)
    corpus = open(sys.argv[1]).read().splitlines()
    qlines = open(sys.argv[2]).read().splitlines()
    slines = open(sys.argv[3]).read().splitlines()
    # keep only non-blank corpus lines, matching the oracles' line-skipping
    corpus = [c for c in corpus if c.strip()]
    n = min(len(corpus), len(qlines), len(slines))
    if not (len(corpus) == len(qlines) == len(slines)):
        print(f"WARNING: length mismatch corpus={len(corpus)} "
              f"qedsvm={len(qlines)} solanalib={len(slines)}; using first {n}")

    buckets = Counter()
    samples = {}
    for i in range(n):
        bucket, sample = classify_pair(corpus[i], qlines[i], slines[i])
        buckets[bucket] += 1
        if sample and bucket not in samples:
            samples[bucket] = (i, corpus[i], qlines[i], slines[i])

    print(f"== {n} vectors ==")
    for bucket, count in sorted(buckets.items(), key=lambda kv: -kv[1]):
        print(f"  {count:6d}  {bucket}")

    hard = sum(c for b, c in buckets.items() if b.startswith("DIVERGE"))
    print(f"\nHARD DIVERGENCES (semantic bug signal): {hard}")
    for bucket in sorted(samples):
        if bucket.startswith("DIVERGE") or bucket.startswith("STRICTER"):
            i, c, q, s = samples[bucket]
            print(f"\n  [{bucket}] line {i}")
            print(f"    corpus:    {c[:120]}{'...' if len(c) > 120 else ''}")
            print(f"    qedsvm:    {q}")
            print(f"    solanalib: {s}")
    sys.exit(1 if hard else 0)


if __name__ == "__main__":
    main()
