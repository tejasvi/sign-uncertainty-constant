#!/usr/bin/env python3
"""Print the properties of the certificates that the paper states, computed from the JSON files in exact arithmetic.

Usage: python3 tests/cert_properties.py certs/cert_r05502_K35.json certs/cert_r05485_X30.json certs/pcert_r05509_NR2.json

For each file: SHA-256, r, the Gaussian pairs (widths with counts, centers per width as an arithmetic progression,
whether all width/center combinations occur, the largest |c|, the smallest power of ten that makes every c an
integer), and, for lower-bound certificates, the cosine terms and the polynomial psi; for upper-bound certificates,
the wide pair T used by the tail argument.  Standard library only.
"""
import hashlib
import json
import sys
from collections import Counter
from fractions import Fraction


def frac(x):
    if not isinstance(x, str):
        raise SystemExit(f"entry {x!r} is not a string of an exact fraction")
    return Fraction(x)


def progression(values):
    v = sorted(set(values))
    if len(v) <= 3:
        return "{" + ", ".join(str(x) for x in v) + "}"
    step = v[1] - v[0]
    ok = all(b - a == step for a, b in zip(v, v[1:]))
    if ok:
        return f"{{{v[0]}, {v[0] + step}, ..., {v[-1]}}} ({len(v)} values, step {step})"
    return "{" + ", ".join(str(x) for x in v) + "}"


def power_of_ten(values):
    """Smallest k <= 16 such that every value times 10^k is an integer, and the values that need more."""
    for k in range(17):
        if all((x * 10 ** k).denominator == 1 for x in values):
            return k, []
    k = 12
    return None, [x for x in values if (x * 10 ** k).denominator != 1]


def is_terminating(x):
    d = x.denominator
    for p in (2, 5):
        while d % p == 0:
            d //= p
    return d == 1


def describe(path):
    raw = open(path, "rb").read()
    d = json.loads(raw)
    print(f"== {path}")
    print(f"sha256 {hashlib.sha256(raw).hexdigest()}")
    r = frac(d["r"])
    print(f"r = {r} = {float(r)}")
    entries = d["gauss"]
    lower = "psi" in d
    if lower:
        assert all(len(e) == 4 and e[3] == 0 or len(e) == 3 for e in entries), "4th field must be 0"
        print(f"fourth fields: {sorted(Counter(e[3] for e in entries if len(e) == 4).items())}")
    G = [(frac(e[0]), frac(e[1]), frac(e[2])) for e in entries]
    print(f"Gaussian pairs: {len(G)}")
    widths = Counter(a for a, _, _ in G)
    print("widths (count): " + ", ".join(f"{a} ({n})" for a, n in sorted(widths.items())))
    for a in sorted(widths):
        print(f"  centers for a = {a}: {progression([s for aa, s, _ in G if aa == a])}")
    cs = [c for _, _, c in G]
    cmax = max(abs(c) for c in cs)
    print(f"max |c| = {cmax} = {float(cmax):.12g}   (< 1000: {cmax < 1000}; < 1: {cmax < 1})")
    k, bad = power_of_ten(cs)
    if k is not None:
        print(f"all c are multiples of 10^-{k}")
    else:
        print(f"c not multiples of 10^-12: {[str(x) for x in bad]}")
    if lower:
        pm = [(frac(b), frac(x)) for b, x in d.get("pm", [])]
        print(f"cosine terms: {len(pm)}")
        if pm:
            print("  beta: " + ", ".join(str(b) for b, _ in pm))
            print("  d:    " + ", ".join(str(x) for _, x in pm))
            print(f"  all beta >= r: {all(b >= r for b, _ in pm)}; all d >= 0: {all(x >= 0 for _, x in pm)}")
            kd, _ = power_of_ten([x for _, x in pm])
            print(f"  all d are multiples of 10^-{kd}")
            dr = [x for b, x in pm if b == r]
            print(f"  d at beta = r: {[str(x) for x in dr]} = {[float(x) for x in dr]}")
            sd = sum(x for _, x in pm)
            print(f"  sum d = {sd} = {float(sd)}")
        q = [frac(z) for z in d["psi"]]
        print(f"psi: {len(q)} coefficients, degree {2 * (len(q) - 1)}; all terminating decimals: {all(is_terminating(z) for z in q)}")
    else:
        amin = min(widths)
        T = [(a, s, c) for a, s, c in G if a == amin]
        print(f"smallest width {amin}: {len(T)} pair(s)")
        aT, sT, cT = T[0]
        smax = max(s for _, s, _ in G)
        print(f"  T = (a, s, c) = ({aT}, {sT}, {cT}); c_T = {float(cT):.12g}; c_T > 0: {cT > 0}; s_T = max s ({smax}): {sT == smax}")
        off = [(a, s, c) for a, s, c in G if (c * 10 ** 12).denominator != 1]
        print(f"  coefficients that are not multiples of 10^-12: {[(str(a), str(s), str(c)) for a, s, c in off]}")
        rest = [(a, s, c) for a, s, c in G if a != amin]
        wr = sorted(set(a for a, _, _ in rest))
        sr = sorted(set(s for _, s, _ in rest))
        combos = set((a, s) for a, s, _ in rest)
        print(f"  other pairs: {len(rest)}; widths {[str(a) for a in wr]}; centers {progression(sr)}; "
              f"all combinations present: {len(combos) == len(wr) * len(sr) == len(rest)}")
    print()


if __name__ == "__main__":
    for p in sys.argv[1:]:
        describe(p)
