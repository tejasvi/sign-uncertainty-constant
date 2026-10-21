#!/usr/bin/env python3
"""Rigorous checker for an UPPER bound on the sign uncertainty constant (+1 case, d = 1).

Certificate: rationals r and (a_j, s_j, c_j), a_j > 0, s_j >= 0.  It defines
    g(x) = sum_j c_j (b_j(x) + bhat_j(x)),
    b_j(x)    = exp(-pi a_j (x - s_j)^2) + exp(-pi a_j (x + s_j)^2),
    bhat_j(x) = 2 a_j^{-1/2} exp(-pi x^2 / a_j) cos(2 pi s_j x)   (the Fourier transform of b_j),
so g is even, in L^1, and ghat = g (F^2 = id on even functions).  The checker proves, in arb ball arithmetic:
    (1) g(0) < 0;
    (2) g(y) > 0 for every y >= r.
Then g is admissible (nonzero, even, g and ghat = g in L^1, g(0) = ghat(0) < 0) with A(g) <= r and A(ghat) <= r, so
A_+(1)^2 <= A(g) A(ghat) <= r^2.  Since g(0) < 0, g also lies in the class of Problem 6.11, so C_6.11 <= r^2.

(2) is split.  On [r, Y]: adaptive Taylor bounds, g(y) >= g(y0) - |g'(y0)| eta - sup|g''/2| eta^2 on [y0-eta, y0+eta],
with sup|g''/2| enclosed by evaluating the Taylor series of g at the ball.  On [Y, inf): the certificate designates a tail
term T (the unique smallest a, a_T, with c_T > 0 and s_T = max s).  Write G(y) = exp(-pi a_T (y - s_T)^2).  For y >= Y every
other piece divided by G is non-increasing (conditions asserted below), so
    g(y)/G(y) >= c_T - sum_{pieces != T main} |coef| * piece(Y)/G(Y) > 0.

Usage: check_primal.py CERT.json [--Y Y] [--workers W] [--w0 1/200] [--depth 30]
"""
import argparse, json, sys, time
from fractions import Fraction
from multiprocessing import Pool

from flint import arb, arb_series, ctx, fmpq

if not __debug__:
    raise SystemExit("this checker relies on assert statements; run it without -O")

PREC = 192


def A(fr):
    fr = Fraction(fr)
    return arb(fmpq(fr.numerator, fr.denominator))


class Cert:
    def __init__(self, path):
        ctx.prec = PREC
        d = json.load(open(path))
        self.r_fr = Fraction(d["r"])
        self.terms = []
        for a, s, c in d["gauss"]:
            af, sf, cf = Fraction(a), Fraction(s), Fraction(c)
            assert af > 0 and sf >= 0
            self.terms.append((af, sf, cf))
        self.pi = arb.pi()
        pi = self.pi
        self.pre = [(pi * A(a), A(s), A(c), 2 * A(c) * A(a).rsqrt(), pi / A(a), 2 * pi * A(s)) for a, s, c in self.terms]

    def series(self, y0, L):
        """Taylor coefficients of g(y0 + t), t^0 .. t^(L-1); y0 may be a ball."""
        Y = arb_series([y0, 1], prec=L)
        tot = arb_series([0], prec=L)
        for (pa, s, c, c2, pia, tps) in self.pre:
            u1 = Y - s
            u2 = Y + s
            tot += c * ((-pa * u1 * u1).exp() + (-pa * u2 * u2).exp()) + c2 * (-pia * Y * Y).exp() * (tps * Y).cos()
        co = tot.coeffs()
        return [co[i] if i < len(co) else arb(0) for i in range(L)]

    def value(self, y0):
        tot = arb(0)
        for (pa, s, c, c2, pia, tps) in self.pre:
            tot += c * ((-pa * (y0 - s) ** 2).exp() + (-pa * (y0 + s) ** 2).exp()) + c2 * (-pia * y0 * y0).exp() * (tps * y0).cos()
        return tot


CERT = None


def init(path):
    global CERT
    CERT = Cert(path)


def ball(lo, hi):
    return A(lo).union(A(hi))


def lb_interval(lo, hi):
    y0 = (lo + hi) / 2
    eta = A((hi - lo) / 2)
    g0, g1 = CERT.series(A(y0), 2)
    g2h = CERT.series(ball(lo, hi), 3)[2]
    return (g0 - abs(g1) * eta - abs(g2h) * eta * eta).lower()


def task(args):
    lo, hi, depth_max = args
    stack = [(lo, hi, 0)]
    worst = None
    n = 0
    while stack:
        a, b, dep = stack.pop()
        lb = lb_interval(a, b)
        n += 1
        if lb > 0:
            worst = float(lb) if worst is None else min(worst, float(lb))
            continue
        if dep >= depth_max:
            return (lo, hi, False, float(lb), n, (float(a), float(b)))
        m = (a + b) / 2
        stack.append((a, m, dep + 1))
        stack.append((m, b, dep + 1))
    return (lo, hi, True, worst, n, None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("--Y", type=str, default=None, help="start of the tail region (default: max s + 12)")
    ap.add_argument("--w0", type=str, default="1/200")
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--depth", type=int, default=30)
    args = ap.parse_args()
    t0 = time.time()
    ctx.prec = PREC
    cert = Cert(args.cert)
    r = cert.r_fr
    pi = cert.pi
    terms = cert.terms
    smax = max(s for _, s, _ in terms)
    Y = Fraction(args.Y) if args.Y else smax + 12
    print(f"r = {r} = {float(r)}; {len(terms)} Gaussian pairs; Y = {Y}", flush=True)
    # (1) g(0) < 0
    g0 = cert.value(arb(0))
    ok0 = g0 < 0
    print(f"g(0) = {g0}  (< 0: {ok0})", flush=True)
    # (3) tail [Y, inf)
    amin = min(a for a, _, _ in terms)
    tails = [(a, s, c) for a, s, c in terms if a == amin]
    assert len(tails) == 1, "need a unique term with the smallest a"
    aT, sT, cT = tails[0]
    assert cT > 0 and sT == smax and Y >= sT
    AT, ST, CT = A(aT), A(sT), A(cT)
    YA = A(Y)
    GY = (-pi * AT * (YA - ST) ** 2).exp()
    bound = arb(0)
    for a, s, c in terms:
        Aa, As, Ac = A(a), A(s), A(c)
        if (a, s, c) == (aT, sT, cT):
            # own mirror term exp(-pi aT (y + sT)^2) is positive (cT > 0): dropped; own hat term:
            # 2 aT^{-1/2} exp(-pi y^2/aT) |cos| / G: exponent derivative 2y/aT - 2 aT (y - sT) > 0 for y >= 0 iff 1/aT > aT
            assert 1 / aT > aT
            bound += abs(Ac) * 2 * Aa.rsqrt() * (-pi * YA * YA / Aa).exp() / GY
            continue
        # b-pieces exp(-pi a (y -+ s)^2)/G non-increasing on [Y, inf): need a > aT and Y >= (a s - aT sT)/(a - aT)
        # (the "+" piece is dominated by the "-" piece for s >= 0); a == aT is impossible (unique smallest a).
        assert a > aT and Y >= (a * s - aT * sT) / (a - aT)
        bound += abs(Ac) * ((-pi * Aa * (YA - As) ** 2).exp() + (-pi * Aa * (YA + As) ** 2).exp()) / GY
        # hat piece 2 a^{-1/2} exp(-pi y^2/a)/G: exponent derivative 2y/a - 2 aT (y - sT) >= 2y (1/a - aT) > 0 needs a < 1/aT
        assert a < 1 / aT
        bound += abs(Ac) * 2 * Aa.rsqrt() * (-pi * YA * YA / Aa).exp() / GY
    tail_lb = CT - bound
    ok_tail = tail_lb > 0
    print(f"tail [Y, inf): g/G >= c_T - (others) = {tail_lb.lower()}  (> 0: {ok_tail})", flush=True)
    # (2) [r, Y]
    w0 = Fraction(args.w0)
    tasks = []
    a = r
    while a < Y:
        b = min(a + w0, Y)
        tasks.append((a, b, args.depth))
        a = b
    ok_mid = True
    worst = None
    nev = 0
    with Pool(args.workers, initializer=init, initargs=(args.cert,)) as pool:
        for lo, hi, ok, val, n, bad in pool.imap_unordered(task, tasks, chunksize=4):
            nev += n
            if not ok:
                ok_mid = False
                print(f"FAIL g on [{float(lo)}, {float(hi)}]: lower bound {val} at {bad}", flush=True)
            else:
                worst = val if worst is None else min(worst, val)
    print(f"g > 0 on [r, Y]: {'PROVED' if ok_mid else 'NOT PROVED'}; smallest local lower bound {worst}; {nev} intervals; "
          f"{time.time()-t0:.0f}s", flush=True)
    allok = ok0 and ok_tail and ok_mid
    print("RESULT:", "PASS" if allok else "FAIL",
          f"=> A_+(1) <= {r} and C_6.11 <= {r*r} = {float(r*r)}" if allok else "", flush=True)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
