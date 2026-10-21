#!/usr/bin/env python3
"""Audit: INDEPENDENT rigorous check of an upper-bound certificate for the +1 sign uncertainty problem (d = 1).
Written by the auditor without reusing check_primal.py; only the certificate format is shared.

Certificate: r and entries [a, s, c] (rationals, a > 0, s >= 0) defining the self-dual function
    g(x) = sum c (b(x) + bhat(x)),  b(x) = exp(-pi a (x-s)^2) + exp(-pi a (x+s)^2),  bhat(x) = 2 a^{-1/2} exp(-pi x^2/a) cos(2 pi s x).
Claim: g(0) < 0 and g(y) > 0 for all y >= r (g is even), hence A_+(1) <= r, C_6.11 <= r^2.

Method (different from check_primal.py):
  * g(0): arb at 256 bits AND mpmath at 60 digits (two libraries).
  * [r, Y]: point values g(y_i) in arb; on [y_i, y_{i+1}] the linear-interpolation bound
        g >= min(g(y_i), g(y_{i+1})) - h^2/8 * sup|g''|,
    with sup|g''| from the explicit second derivative evaluated on the ball [y_i, y_{i+1}]; adaptive bisection.
  * [Y, inf): every piece p other than the dominant term T (smallest a, c_T > 0, s_T = max s) satisfies
        |p(y)| / G(y) <= exp(-Q_p(y)),  G(y) = exp(-pi a_T (y - s_T)^2),
    with Q_p a quadratic with positive leading coefficient; Q_p is increasing on [vertex_p, inf), so for Y >= vertex_p the
    ratio is at most exp(-Q_p(Y)) on [Y, inf).  Vertices and leading coefficients are computed explicitly (exact rationals)
    and asserted.  Then g/G >= c_T - sum |coef_p| exp(-Q_p(Y)) on [Y, inf) (T's mirror piece is >= 0 and dropped).
    As a redundant check, g > 0 is also proved directly on [Y, Y2] by the interval method.
Usage: indep_primal.py CERT.json [--Y 32] [--Y2 64] [--workers 20] [--h0 1/500]
"""
import argparse, json, sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool

from flint import arb, ctx, fmpq
import mpmath as mp

if not __debug__:
    raise SystemExit("this checker relies on assert statements; run it without -O")

PREC = 256


def A(x):
    x = Fr(x)
    return arb(fmpq(x.numerator, x.denominator))


class G:
    def __init__(self, path):
        ctx.prec = PREC
        d = json.load(open(path))
        self.r = Fr(d["r"])
        self.T = []
        for e in d["gauss"]:
            assert len(e) == 3
            a, s, c = Fr(e[0]), Fr(e[1]), Fr(e[2])
            assert a > 0 and s >= 0
            self.T.append((a, s, c))
        pi = arb.pi()
        self.pi = pi
        self.P = [(A(c), pi * A(a), A(s), 2 * A(c) / A(a).sqrt(), pi / A(a), 2 * pi * A(s), A(a)) for a, s, c in self.T]

    def g(self, y):
        tot = arb(0)
        for c, pa, s, c2, pia, tps, a in self.P:
            # u*u, not u**2: python-flint returns nan for (ball containing 0)**2, e.g. at y = s exactly
            u1 = y - s; u2 = y + s
            tot += c * ((-pa * u1 * u1).exp() + (-pa * u2 * u2).exp()) + c2 * (-pia * y * y).exp() * (tps * y).cos()
        return tot

    def g2(self, y):
        """explicit second derivative of g."""
        tot = arb(0)
        pi = self.pi
        for c, pa, s, c2, pia, tps, a in self.P:
            for u in (y - s, y + s):
                tot += c * (4 * pa * pa * u * u - 2 * pa) * (-pa * u * u).exp()
            E = (-pia * y * y).exp()
            E1 = -2 * pia * y * E
            E2 = (4 * pia * pia * y * y - 2 * pia) * E
            C = (tps * y).cos(); S = (tps * y).sin()
            tot += c2 * (E2 * C - 2 * E1 * tps * S - E * tps * tps * C)
        return tot


GG = None


def init(path):
    global GG
    GG = G(path)


def ball(lo, hi):
    return A(lo).union(A(hi))


def task(args):
    lo, hi, h0, maxdepth = args
    pts = [lo]
    while pts[-1] < hi:
        pts.append(min(pts[-1] + h0, hi))
    cache = {}

    def gv(t):
        if t not in cache:
            cache[t] = GG.g(A(t))
        return cache[t]

    stack = [(pts[i], pts[i + 1], 0) for i in range(len(pts) - 1)]
    worst = None
    n = 0
    while stack:
        a, b, dep = stack.pop()
        h = A(b - a)
        lb = gv(a).union(gv(b)).lower() - h * h / 8 * abs(GG.g2(ball(a, b)))
        n += 1
        if lb > 0:
            v = float(lb.lower().mid())
            worst = v if worst is None else min(worst, v)
            continue
        if dep >= maxdepth:
            return (lo, hi, False, float(lb.lower().mid()), (float(a), float(b)), n)
        m = (a + b) / 2
        stack.append((a, m, dep + 1)); stack.append((m, b, dep + 1))
    return (lo, hi, True, worst, None, n)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("--Y", default=None)
    ap.add_argument("--Y2", default=None)
    ap.add_argument("--workers", type=int, default=20)
    ap.add_argument("--h0", default="1/500")
    ap.add_argument("--chunk", default="1/4")
    ap.add_argument("--depth", type=int, default=30)
    args = ap.parse_args()
    t0 = time.time()
    ctx.prec = PREC
    C = G(args.cert)
    r = C.r
    smax = max(s for _, s, _ in C.T)
    Y = Fr(args.Y) if args.Y else smax + 12
    Y2 = Fr(args.Y2) if args.Y2 else 2 * Y
    print(f"[indep-primal] r = {r} = {float(r)}; {len(C.T)} pairs; Y = {Y}, Y2 = {Y2}", flush=True)
    # (1) g(0) < 0, two libraries
    g0 = C.g(arb(0))
    mp.mp.dps = 60
    g0m = mp.mpf(0)
    for a, s, c in C.T:
        am, sm, cm = (mp.mpf(z.numerator) / z.denominator for z in (a, s, c))
        g0m += cm * (2 * mp.exp(-mp.pi * am * sm * sm) + 2 / mp.sqrt(am))
    ok0 = g0 < 0
    print(f"[indep-primal] g(0) arb = {g0.str(20)}; mpmath(60 digits) = {mp.nstr(g0m, 20)}; < 0: {ok0 and g0m < 0}", flush=True)
    ok0 = ok0 and g0m < 0
    # (2) tail argument
    aT = min(a for a, _, _ in C.T)
    Ts = [(a, s, c) for a, s, c in C.T if a == aT]
    assert len(Ts) == 1, "dominant term must be unique"
    aT, sT, cT = Ts[0]
    assert cT > 0 and sT == smax and aT < 1 and Y >= sT
    pi = C.pi
    tail = A(cT)
    worst_vertex = Fr(-10 ** 9)
    for a, s, c in C.T:
        isT = (a, s, c) == (aT, sT, cT)
        pieces = []
        if not isT:
            # b pieces exp(-pi a (y - sig s)^2), sig = +1, -1:  Q = pi[(a - aT) y^2 - 2(a sig s - aT sT) y + a s^2 - aT sT^2]
            for sig in (1, -1):
                lead = a - aT
                assert lead > 0
                vert = (a * sig * s - aT * sT) / lead
                pieces.append(("b", sig, vert))
        # hat piece 2 a^{-1/2} exp(-pi y^2/a) |cos|:  Q = pi[(1/a - aT) y^2 + 2 aT sT y - aT sT^2]
        lead = 1 / a - aT
        assert lead > 0
        vert = -aT * sT / lead
        pieces.append(("h", 0, vert))
        for kind, sig, vert in pieces:
            assert Y >= vert, (a, s, kind, vert)
            worst_vertex = max(worst_vertex, vert)
            YA = A(Y)
            dT = YA - A(sT)
            QY = pi * A(aT) * dT * dT                    # -log G(Y)
            if kind == "b":
                du = YA - sig * A(s)
                val = (-pi * A(a) * du * du + QY).exp()
            else:
                val = 2 / A(a).sqrt() * (-pi * YA * YA / A(a) + QY).exp()
            tail -= abs(A(c)) * val
    ok_tail = tail > 0
    print(f"[indep-primal] tail: g/G >= {tail.str(15)} on [Y, inf) (largest vertex {float(worst_vertex):.4f} <= Y = {Y}); "
          f"> 0: {ok_tail}", flush=True)
    # (3) [r, Y2] by interpolation bounds (the part [Y, Y2] is redundant with the tail argument)
    ch = Fr(args.chunk); h0 = Fr(args.h0)
    tasks = []
    a = r
    while a < Y2:
        b = min(a + ch, Y2)
        tasks.append((a, b, h0, args.depth))
        a = b
    ok_mid = True
    worst = None
    nev = 0
    with Pool(args.workers, initializer=init, initargs=(args.cert,)) as pool:
        for lo, hi, ok, val, bad, n in pool.imap_unordered(task, tasks, chunksize=2):
            nev += n
            if not ok:
                ok_mid = False
                print(f"[indep-primal] FAIL g on [{float(lo)}, {float(hi)}]: bound {val} at {bad}", flush=True)
            else:
                worst = val if worst is None else min(worst, val)
    print(f"[indep-primal] g > 0 on [r, Y2]: {'PROVED' if ok_mid else 'NOT PROVED'}; smallest local lower bound {worst}; "
          f"{nev} intervals; {time.time()-t0:.0f}s", flush=True)
    allok = ok0 and ok_tail and ok_mid
    print(f"[indep-primal] RESULT: {'PASS' if allok else 'FAIL'}" + (f"  (A_+(1) <= {r}, C_6.11 <= {r*r} = {float(r*r)})" if allok else ""),
          flush=True)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
