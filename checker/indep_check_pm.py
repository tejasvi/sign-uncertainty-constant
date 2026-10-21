#!/usr/bin/env python3
"""Audit: INDEPENDENT rigorous re-check of a sign-uncertainty dual certificate (written by the auditor, without
reusing check_cert.py; only the certificate data format and the Lemma's statement are shared).

Lemma (PROGRESS.md): with v = sum c (b - bhat), phi = 1 - v + psi on I = [-r, r], W = 1 - v + F phi on |y| > r,
rho = F phi - psi on I, kappa >= ||K||_HS (K = cos(2 pi x y) kernel on I x I):
   kappa < 1,  W >= m on (r, inf),  |rho| <= e on [0, r],  m > 2 r e / (1 - kappa)   ==>   A_+(1) > r.

Method (different from check_cert.py):
  * F phi in CLOSED FORM:  F 1 = sin(2 pi r y)/(pi y);  F psi = 2 Re[e^{i w r} sum_j (-1)^j psi^(j)(r)/(i w)^{j+1}]
    (exact; w = 2 pi y) for w r >= 10, exact power series with a geometric tail bound for w r < 10;
    Gaussians via complex erf (acb):  int_I e^{-pi a (x-s)^2} e^{2 pi i x y} dx
       = e^{2 pi i s y} e^{-pi y^2/a} /(2 sqrt a) [erf(sqrt(pi a)(r-s) - i sqrt(pi/a) y) - erf(sqrt(pi a)(-r-s) - i sqrt(pi/a) y)].
  * Interval lower bounds by linear interpolation: f >= min(f(y0), f(y1)) - (y1-y0)^2/8 * sup|f''|, with
    sup|W''| <= sup|v''| (ball evaluation of the explicit second derivative) + C2,  C2 = 4 pi^2 int_I |phi| x^2 dx;
    similarly |rho| <= max(|rho(x0)|, |rho(x1)|) + h^2/8 (C2 + sup|psi''|).  Adaptive bisection.
  * Tail y >= YT: n-fold integration by parts with phi^(k)(r) from explicit Hermite-polynomial derivative formulas
    and int_0^r |phi^(n)| bounded on subintervals by ball evaluation.
  * kappa^2 = 2 r^2 + Si(4 pi r^2)/(2 pi) bounded in exact rational arithmetic (rational bounds for pi, alternating
    Taylor series of Si, Si decreasing on [pi, 2 pi]).
Point-mass extension (audit of the r = 11/20 certificate): entries "pm": [[beta, d], ...] with beta >= r, d >= 0 add
  sum d (cos(2 pi beta x) - (delta_beta + delta_-beta)/2) to v; v_ac contains sum d cos(2 pi beta x), phi = 1 - v_ac + psi,
  W = 1 - v_ac + F phi, and the identity gains + sum d g(beta) >= 0 (g continuous, >= 0 on |x| >= r).
  Closed form: int_I cos(2 pi beta x) cos(2 pi y x) dx = r [sinc(2 pi r (beta - y)) + sinc(2 pi r (beta + y))].
  Tail: |sum d cos| <= sum d.  For y >= 20 the bound on |F phi''| is min(C2, 8 pi^2 B2(2 pi y)), where B2 is the 4-fold
  integration-by-parts bound for int_0^r x^2 phi(x) cos(w x) dx (x^2 phi is even, so odd derivatives vanish at 0).
Usage: indep_check_pm.py CERT.json --m 1/2500 --e 1/100000 --YT 1500 --nibp 8 --workers 36
"""
import argparse, json, math, sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool

from flint import arb, acb, ctx, fmpq

if not __debug__:
    raise SystemExit("this checker relies on assert statements; run it without -O")

PREC = 256


def A(x):
    x = Fr(x)
    return arb(fmpq(x.numerator, x.denominator))


class Cert:
    def __init__(self, path):
        ctx.prec = PREC
        d = json.load(open(path))
        self.r_fr = Fr(d["r"])
        assert all(len(e) == 3 or (len(e) == 4 and int(e[3]) == 0) for e in d["gauss"])
        self.G_fr = [(Fr(e[0]), Fr(e[1]), Fr(e[2])) for e in d["gauss"]]
        self.pm_fr = [(Fr(b), Fr(dd)) for b, dd in d.get("pm", [])]
        for b, dd in self.pm_fr:
            assert b >= Fr(d["r"]) and dd >= 0, (b, dd)
        self.pm_sum = sum((dd for _, dd in self.pm_fr), Fr(0))
        self.q_fr = [Fr(z) for z in d["psi"]]
        self.r = A(self.r_fr)
        self.pi = arb.pi()
        self.pm = [(A(b), A(dd), 2 * arb.pi() * A(b)) for b, dd in self.pm_fr]   # (beta, d, 2 pi beta)
        pi = self.pi
        self.G = []
        for a, s, c in self.G_fr:
            assert a > 0 and s >= 0
            aa, ss, cc = A(a), A(s), A(c)
            self.G.append(dict(a=aa, s=ss, c=cc, ra=aa.sqrt(), pa=pi * aa, pia=pi / aa,
                               spa=(pi * aa).sqrt(), spia=(pi / aa).sqrt(), tps=2 * pi * ss))
        # psi^(j)(r) exactly (rational), j = 0..deg
        deg = 2 * (len(self.q_fr) - 1)
        coef = [Fr(0)] * (deg + 1)
        for k, qk in enumerate(self.q_fr):
            coef[2 * k] = qk
        self.psi_coef = coef
        self.psider_r = []
        cur = coef[:]
        for j in range(deg + 1):
            val = sum(cj * self.r_fr ** i for i, cj in enumerate(cur))
            self.psider_r.append(A(val))
            cur = [i * cur[i] for i in range(1, len(cur))]

    # ---------------- real-line functions (arb point or ball arguments) ----------------
    def v(self, y):
        tot = arb(0)
        for g in self.G:
            u1 = y - g["s"]; u2 = y + g["s"]
            tot += g["c"] * ((-g["pa"] * u1 * u1).exp() + (-g["pa"] * u2 * u2).exp()
                             - 2 / g["ra"] * (-g["pia"] * y * y).exp() * (g["tps"] * y).cos())
        for b, dd, tb in self.pm:
            tot += dd * (tb * y).cos()
        return tot

    def v2(self, y):
        """second derivative of v (explicit formulas)."""
        tot = arb(0)
        pi = self.pi
        for g in self.G:
            a = g["a"]
            part = arb(0)
            for u in (y - g["s"], y + g["s"]):
                part += (4 * pi * pi * a * a * u * u - 2 * pi * a) * (-g["pa"] * u * u).exp()
            E = (-g["pia"] * y * y).exp()
            E1 = -2 * pi * y / a * E
            E2 = ((2 * pi * y / a) ** 2 - 2 * pi / a) * E
            C = (g["tps"] * y).cos(); S = (g["tps"] * y).sin()
            C1 = -g["tps"] * S
            C2 = -g["tps"] * g["tps"] * C
            part -= 2 / g["ra"] * (E2 * C + 2 * E1 * C1 + E * C2)
            tot += g["c"] * part
        for b, dd, tb in self.pm:
            tot -= dd * tb * tb * (tb * y).cos()
        return tot

    def psi(self, x):
        p = arb(0)
        x2 = x * x
        for qk in reversed(self.q_fr):
            p = p * x2 + A(qk)
        return p

    def psi2(self, x):
        p = arb(0)
        n = len(self.psi_coef)
        for i in range(n - 1, 1, -1):
            p = p * x + A(i * (i - 1) * self.psi_coef[i])
        return p

    def phi(self, x):
        return 1 - self.v(x) + self.psi(x)

    # ---------------- closed-form F phi(y) at a point y (arb) ----------------
    def F1(self, y):
        if y.is_zero():
            return 2 * self.r
        return (2 * self.pi * self.r * y).sin() / (self.pi * y)

    def Fpsi(self, y):
        w = 2 * self.pi * y
        wr = w * self.r
        if abs(wr) < 10:
            # sum_k q_k J_{2k}(y), J_n = sum_m (-1)^m w^{2m}/(2m)! * 2 r^{n+2m+1}/(n+2m+1)
            tot = arb(0)
            r = self.r
            for k, qk in enumerate(self.q_fr):
                if qk == 0:
                    continue
                n = 2 * k
                M = 60
                s = arb(0)
                term_fac = arb(1)          # w^{2m}/(2m)!
                for m in range(M):
                    if m > 0:
                        term_fac = term_fac * w * w / ((2 * m - 1) * (2 * m))
                    s += (-1) ** m * term_fac * 2 * r ** (n + 2 * m + 1) / (n + 2 * m + 1)
                # tail m >= M: |terms| <= T_M / (1 - rho), rho = (w r)^2 / ((2M+1)(2M+2)) (all later ratios smaller)
                T_M = term_fac * w * w / ((2 * M - 1) * (2 * M)) * 2 * r ** (n + 2 * M + 1) / (n + 2 * M + 1)
                rho = wr * wr / ((2 * M + 1) * (2 * M + 2))
                assert rho < 1
                tail = abs(T_M) / (1 - rho)
                s += arb(0, tail.upper())
                tot += A(qk) * s
            return tot
        iw = acb(0, w)
        S = acb(0)
        p = iw
        for j, dj in enumerate(self.psider_r):
            S += (-1) ** j * dj / p
            p = p * iw
        e = acb(0, w * self.r).exp()
        return 2 * (e * S).real

    def Fv(self, y):
        pi = self.pi
        r = self.r
        tot = arb(0)
        for g in self.G:
            a, s = g["a"], g["s"]
            # 2 Re G(a, s, y) = int_I (e^{-pi a (x-s)^2} + e^{-pi a (x+s)^2}) cos(2 pi x y) dx
            t2 = acb(g["spa"] * (r - s), -g["spia"] * y)
            t1 = acb(g["spa"] * (-r - s), -g["spia"] * y)
            Gv = acb(0, 2 * pi * s * y).exp() * (-g["pia"] * y * y).exp() / (2 * g["ra"]) * (t2.erf() - t1.erf())
            Fb = 2 * Gv.real
            # int_I bhat cos(2 pi x y) = H(s + y) + H(s - y),  H(y') = e^{-pi a y'^2} Re erf(sqrt(pi/a) r - i sqrt(pi a) y')
            Fbh = arb(0)
            for yp in (s + y, s - y):
                z = acb(g["spia"] * r, -g["spa"] * yp)
                Fbh += (-g["pa"] * yp * yp).exp() * z.erf().real
            tot += g["c"] * (Fb - Fbh)
        # point-mass cosines: int_I cos(2 pi beta x) cos(2 pi y x) dx = r [sinc(2 pi r (beta - y)) + sinc(2 pi r (beta + y))]
        for b, dd, tb in self.pm:
            tot += dd * r * ((2 * pi * r * (b - y)).sinc() + (2 * pi * r * (b + y)).sinc())
        return tot

    def Fphi(self, y):
        return self.F1(y) - self.Fv(y) + self.Fpsi(y)

    def W(self, y):
        return 1 - self.v(y) + self.Fphi(y)

    def rho(self, x):
        return self.Fphi(x) - self.psi(x)

    # ---------------- derivatives of phi for the tail ----------------
    def dphi(self, x, n):
        """n-th derivative of phi at x (arb point or ball), explicit Hermite formulas."""
        pi = self.pi
        tot = arb(1) if n == 0 else arb(0)

        def herm_real(n_, t):          # physicists' Hermite H_n(t), arb
            h0, h1 = arb(1), 2 * t
            if n_ == 0:
                return h0
            for k in range(1, n_):
                h0, h1 = h1, 2 * t * h1 - 2 * k * h0
            return h1

        def herm_cplx(n_, t):
            h0, h1 = acb(1), 2 * t
            if n_ == 0:
                return h0
            for k in range(1, n_):
                h0, h1 = h1, 2 * t * h1 - 2 * k * h0
            return h1

        for g in self.G:
            a, s, c = g["a"], g["s"], g["c"]
            dv = arb(0)
            for u in (x - s, x + s):
                dv += (-g["spa"]) ** n * herm_real(n, g["spa"] * u) * (-g["pa"] * u * u).exp()
            z = acb(x, -a * s)
            dh = 2 / g["ra"] * ((-pi * a * s * s).exp() * (-g["spia"]) ** n * herm_cplx(n, g["spia"] * z)
                                * (-(pi / a) * z * z).exp()).real
            tot -= c * (dv - dh)
        # point-mass cosines: d^n/dx^n cos(w x) = w^n * (cos, -sin, -cos, sin)[n mod 4](w x)
        for b, dd, tb in self.pm:
            z = tb * x
            trig = [z.cos(), -z.sin(), -z.cos(), z.sin()][n % 4]
            tot -= dd * tb ** n * trig
        # psi
        cur = self.psi_coef[:]
        for _ in range(n):
            cur = [i * cur[i] for i in range(1, len(cur))]
        p = arb(0)
        for cj in reversed(cur):
            p = p * x + A(cj)
        return tot + p


CERT = None


def init(path):
    global CERT
    CERT = Cert(path)


def ballr(lo, hi):
    return A(lo).union(A(hi))


def up_fr(x):
    """exact rational upper bound of an arb (via its exact upper endpoint)."""
    m_, e_ = x.upper().man_exp()
    return Fr(int(m_)) * Fr(2) ** int(e_)


def task_C2(args):
    lo, hi = args
    J = ballr(lo, hi)
    ph = abs(CERT.phi(J))
    return str(up_fr(ph * (A(hi) ** 3 - A(lo) ** 3) / 3))


def task_W(args):
    """Prove W >= m on [lo, hi] with initial grid step h0; adaptive bisection."""
    lo, hi, h0, m, C2s, maxdepth, far = args
    m = A(Fr(m)); C2 = A(Fr(C2s))
    # far = (chi_abs[0..3], Jchi4) as strings, or None: |F phi''(y)| <= 8 pi^2 B2(2 pi y), B2 decreasing in y
    if far is not None:
        chi_abs = [A(Fr(z)) for z in far[0]]
        Jchi4 = A(Fr(far[1]))

        def M2F(y):
            w = 2 * CERT.pi * A(y)
            B2 = sum((chi_abs[k] / w ** (k + 1) for k in range(4)), arb(0)) + Jchi4 / w ** 4
            return 8 * CERT.pi * CERT.pi * B2
    pts = []
    y = lo
    while y < hi:
        pts.append(y)
        y = min(y + h0, hi)
    pts.append(hi)
    cache = {}

    def Wv(t):
        if t not in cache:
            cache[t] = CERT.W(A(t))
        return cache[t]

    worst = None
    nev = 0
    stack = [(pts[i], pts[i + 1], 0) for i in range(len(pts) - 1)]
    while stack:
        a, b, dep = stack.pop()
        h = A(b - a)
        MF = C2
        if far is not None and a >= 20:
            mf = M2F(a)
            if mf < C2:
                MF = mf
        M2 = abs(CERT.v2(ballr(a, b))) + MF
        wa, wb = Wv(a), Wv(b)
        lb = wa.union(wb).lower() - h * h / 8 * M2      # <= min(W(a), W(b)) - h^2/8 sup|W''|
        nev += 1
        if lb > m:
            fl = float(lb.lower().mid())
            worst = fl if worst is None else min(worst, fl)
            continue
        if dep >= maxdepth:
            return (lo, hi, False, float(lb.lower().mid()), (float(a), float(b)), nev)
        mid = (a + b) / 2
        stack.append((a, mid, dep + 1)); stack.append((mid, b, dep + 1))
    return (lo, hi, True, worst, None, nev)


def task_rho(args):
    lo, hi, h0, e, C2s, maxdepth = args
    e = A(Fr(e)); C2 = A(Fr(C2s))
    pts = []
    x = lo
    while x < hi:
        pts.append(x)
        x = min(x + h0, hi)
    pts.append(hi)
    cache = {}

    def rv(t):
        if t not in cache:
            cache[t] = abs(CERT.rho(A(t)))
        return cache[t]

    worst = None
    stack = [(pts[i], pts[i + 1], 0) for i in range(len(pts) - 1)]
    while stack:
        a, b, dep = stack.pop()
        h = A(b - a)
        M2 = C2 + abs(CERT.psi2(ballr(a, b)))
        ub = rv(a).union(rv(b)).upper() + h * h / 8 * M2
        if ub < e:
            fu = float(ub.upper().mid())
            worst = fu if worst is None else max(worst, fu)
            continue
        if dep >= maxdepth:
            return (lo, hi, False, float(ub.upper().mid()), (float(a), float(b)))
        mid = (a + b) / 2
        stack.append((a, mid, dep + 1)); stack.append((mid, b, dep + 1))
    return (lo, hi, True, worst, None)


def task_dn(args):
    lo, hi, n = args
    J = ballr(lo, hi)
    d = abs(CERT.dphi(J, n)) * A(hi - lo)
    return str(up_fr(d))


def task_dnw(args):
    """upper bound for int_lo^hi x^p |phi^(n)(x)| dx (0 <= lo < hi)."""
    lo, hi, n, p = args
    J = ballr(lo, hi)
    d = abs(CERT.dphi(J, n)) * (A(hi) ** (p + 1) - A(lo) ** (p + 1)) / (p + 1)
    return str(up_fr(d))


def kappa_upper(r):
    """Rational upper bound for sqrt(2 r^2 + Si(4 pi r^2)/(2 pi)); requires pi < 4 pi r^2 < 2 pi."""
    pi_lo = Fr(314159265358979323846, 10 ** 20)
    pi_hi = Fr(314159265358979323847, 10 ** 20)
    x_lo = 4 * pi_lo * r * r
    assert pi_hi < x_lo and 4 * pi_hi * r * r < 2 * pi_lo   # Si decreasing on [pi, 2 pi]: Si(x) <= Si(x_lo)
    # Si(x_lo) = sum (-1)^n x^(2n+1)/((2n+1)(2n+1)!); alternating with eventually decreasing terms
    S = Fr(0)
    terms = []
    for n in range(60):
        t = x_lo ** (2 * n + 1) / ((2 * n + 1) * math.factorial(2 * n + 1))
        terms.append(t)
        S += (-1) ** n * t
    assert all(terms[i + 1] < terms[i] for i in range(10, 59))
    Si_up = S + terms[-1]
    k2 = 2 * r * r + Si_up / (2 * pi_lo)
    # rational sqrt upper bound
    D = 10 ** 30
    k = Fr(math.isqrt(math.ceil(k2 * D * D)) + 1, D)
    assert k * k >= k2
    return k, k2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("--m", default="1/2500")
    ap.add_argument("--e", default="1/100000")
    ap.add_argument("--YT", default="1500")
    ap.add_argument("--nibp", type=int, default=8)
    ap.add_argument("--workers", type=int, default=30)
    ap.add_argument("--h0", default="1/1000")
    ap.add_argument("--h0far", default="1/400", help="initial step for y >= 20")
    ap.add_argument("--chunk", default="1/4")
    ap.add_argument("--hrho", default="1/100000")
    ap.add_argument("--nsubC2", type=int, default=4000)
    ap.add_argument("--nsubdn", type=int, default=20000)
    ap.add_argument("--skipW", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    ctx.prec = PREC
    C = Cert(args.cert)
    r = C.r_fr
    m = Fr(args.m); e = Fr(args.e); YT = Fr(args.YT)
    assert all(s <= YT for _, s, _ in C.G_fr)
    print(f"[indep] r = {r}; {len(C.G_fr)} pairs; psi deg {2*(len(C.q_fr)-1)}; m = {m}, e = {e}, YT = {YT}", flush=True)
    # (1) kappa
    k_up, k2 = kappa_upper(r)
    print(f"[indep] kappa <= {k_up} = {float(k_up):.15f}", flush=True)
    assert k_up < 1
    pool = Pool(args.workers, initializer=init, initargs=(args.cert,))
    # (2) C2 = 4 pi^2 int_{-r}^{r} |phi| x^2 = 8 pi^2 int_0^r |phi| x^2
    ns = args.nsubC2
    I2 = sum(Fr(z) for z in pool.map(task_C2, [(r * i / ns, r * (i + 1) / ns) for i in range(ns)], chunksize=20))
    C2 = 8 * Fr(31415926535897932385, 10 ** 19) ** 2 * I2
    print(f"[indep] int_0^r |phi| x^2 <= {float(I2):.6g};  C2 = sup|F phi''| bound <= {float(C2):.6g}", flush=True)
    # (3) tail: |int_0^r phi cos(w x)| <= sum_{k<n} |phi^(k)(r)|/w^(k+1) + w^-n int_0^r |phi^(n)|
    n = args.nibp
    der = [C.dphi(C.r, k) for k in range(n)]
    nd = args.nsubdn
    In = sum(Fr(z) for z in pool.map(task_dn, [(r * i / nd, r * (i + 1) / nd, n) for i in range(nd)], chunksize=50))
    om = 2 * C.pi * A(YT)
    B = arb(0)
    for k in range(n):
        B += abs(der[k]) / om ** (k + 1)
    B += A(In) / om ** n
    VT = arb(0)
    for g in C.G:
        VT += abs(g["c"]) * ((-g["pa"] * (A(YT) - g["s"]) ** 2).exp() + (-g["pa"] * (A(YT) + g["s"]) ** 2).exp()
                             + 2 / g["ra"] * (-g["pia"] * A(YT) * A(YT)).exp())
    tail = 1 - A(C.pm_sum) - VT - 2 * B          # |sum d cos(2 pi beta y)| <= sum d
    print(f"[indep] pm terms: {len(C.pm_fr)}, sum d = {C.pm_sum} = {float(C.pm_sum)}; betas >= r and d >= 0 asserted", flush=True)
    print(f"[indep] phi^(k)(r): {[float(d.mid()) for d in der]}", flush=True)
    print(f"[indep] int_0^r |phi^({n})| <= {float(In):.6g};  tail: W >= {float(tail.lower().mid()):.6f} on [YT, inf)",
          flush=True)
    tail_ok = tail > A(m)
    # (3b) far-field bound for |F phi''|: chi = x^2 phi, F phi''(y) = -(2 pi)^2 * 2 int_0^r chi(x) cos(w x) dx;
    #      4-fold IBP: |int_0^r chi cos| <= sum_{k<4} |chi^(k)(r)|/w^(k+1) + w^-4 int_0^r |chi^(4)|,
    #      chi^(k) = x^2 phi^(k) + 2k x phi^(k-1) + k(k-1) phi^(k-2);
    #      int |chi^(4)| <= int x^2 |phi^(4)| + 8 int x |phi^(3)| + 12 int |phi^(2)|
    rr = C.r
    chi = []
    for k in range(4):
        val = rr * rr * der[k]
        if k >= 1:
            val += 2 * k * rr * der[k - 1]
        if k >= 2:
            val += k * (k - 1) * der[k - 2]
        chi.append(str(up_fr(abs(val))))
    Jw = {}
    for (nn, pp) in ((4, 2), (3, 1), (2, 0)):
        Jw[(nn, pp)] = sum(Fr(z) for z in pool.map(task_dnw, [(r * i / nd, r * (i + 1) / nd, nn, pp) for i in range(nd)],
                                                     chunksize=50))
    Jchi4 = Jw[(4, 2)] + 8 * Jw[(3, 1)] + 12 * Jw[(2, 0)]
    far = ([z for z in chi], str(Jchi4))
    print(f"[indep] far-field F phi'' bound: |chi^(k)(r)| <= {[float(Fr(z)) for z in chi]}, int|chi^(4)| <= {float(Jchi4):.4g}",
          flush=True)
    # (4) W >= m on [r, YT]
    W_ok = True
    worst = None
    nev = 0
    if not args.skipW:
        ch = Fr(args.chunk); h0 = Fr(args.h0); h0far = Fr(args.h0far)
        tasks = []
        a = r
        while a < YT:
            b = min(a + ch, YT)
            tasks.append((a, b, h0 if a < 20 else h0far, str(m), str(C2), 22, far))
            a = b
        for res in pool.imap_unordered(task_W, tasks, chunksize=1):
            lo, hi, ok, val, bad, ne = res
            nev += ne
            if not ok:
                W_ok = False
                print(f"[indep] FAIL W on [{float(lo)}, {float(hi)}]: bound {val} at {bad}", flush=True)
            else:
                worst = val if worst is None else min(worst, val)
        print(f"[indep] W on [r, YT]: {'PROVED' if W_ok else 'NOT PROVED'} >= {float(m)}; smallest local lower bound "
              f"{worst}; {nev} intervals; {time.time()-t0:.0f}s", flush=True)
    else:
        W_ok = False
        print("[indep] W check skipped", flush=True)
    # (5) |rho| <= e on [0, r]
    hr = Fr(args.hrho)
    tasks = []
    a = Fr(0)
    nch = 40
    for i in range(nch):
        tasks.append((r * i / nch, r * (i + 1) / nch, hr, str(e), str(C2), 22))
    rho_ok = True
    rworst = None
    for res in pool.imap_unordered(task_rho, tasks, chunksize=1):
        lo, hi, ok, val, bad = res
        if not ok:
            rho_ok = False
            print(f"[indep] FAIL rho on [{float(lo)}, {float(hi)}]: bound {val} at {bad}", flush=True)
        else:
            rworst = val if rworst is None else max(rworst, val)
    print(f"[indep] sup|rho| on [0, r]: {'PROVED' if rho_ok else 'NOT PROVED'} <= {float(e)}; largest local bound {rworst}",
          flush=True)
    pool.close()
    # (6) final
    final_ok = m > 2 * r * e / (1 - k_up)
    print(f"[indep] final: m = {float(m)} > 2 r e/(1 - kappa) = {float(2*r*e/(1-k_up)):.6g}: {final_ok}", flush=True)
    allok = W_ok and tail_ok and rho_ok and final_ok
    print(f"[indep] RESULT: {'PASS' if allok else 'FAIL'}  (A_+(1) > {r})" if allok else "[indep] RESULT: FAIL", flush=True)
    print(f"[indep] total {time.time()-t0:.0f}s")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
