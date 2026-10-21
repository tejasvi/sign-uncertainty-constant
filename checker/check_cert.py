#!/usr/bin/env python3
"""Independent rigorous checker for a dual certificate of the +1 sign uncertainty principle in d = 1.

Statement checked (Lemma "certificate" in ../PROGRESS.md):
  Let r > 0, I = [-r, r], O = R minus I.  Let v = sum_j c_j (b_j - bhat_j) with Gaussian pairs
      b_j(x)    = exp(-pi a_j (x - s_j)^2) + exp(-pi a_j (x + s_j)^2),
      bhat_j(y) = 2 a_j^{-1/2} exp(-pi y^2 / a_j) cos(2 pi s_j y)       (Fourier transform of b_j),
  so that the Fourier transform of v is -v.  Let psi(x) = sum_k q_k x^(2k) and
      phi(x) = 1 - v(x) + psi(x) on I (phi = 0 on O),
      (F phi)(y) = int_I phi(x) cos(2 pi x y) dx,
      W(y)   = 1 - v(y) + (F phi)(y)       (y in O),
      rho(x) = (F phi)(x) - psi(x)         (x in I)   [= 1 - v - phi + K phi on I].
  Let kappa = sqrt(2 r^2 + Si(4 pi r^2)/(2 pi)) (Hilbert-Schmidt norm of K, kernel cos(2 pi x y) on I x I).
  If kappa < 1 and  inf_{y > r} W(y) >= m  and  sup_{0 <= x <= r} |rho(x)| <= e  with  m > 2 r e / (1 - kappa),
  then every g in L^1(R) with ghat = g, g(0) <= 0 and g >= 0 a.e. on O vanishes, hence A_+(1) > r and
  C_{6.11} >= A_+(1)^2 > r^2.

Everything below is computed in ball arithmetic (python-flint arb).  F phi and its y-derivatives are computed by
Gauss-Legendre quadrature on [0, r] with nodes/weights from arb's legendre_p_root, plus a rigorous error bound:
for F analytic in the Bernstein ellipse E_rho with |F| <= M there, the N-point Gauss-Legendre error on [-1, 1] is
at most 4 sum_{k >= 2N} |a_k| <= 8 M rho^{-2N} / (1 - 1/rho)  (|a_k| <= 2 M rho^{-k} for Chebyshev coefficients;
the rule is exact for degree <= 2N-1; |int T_k| <= 2, sum of weights = 2).

Usage: check_cert.py CERT.json --m 0.02 [--N 500] [--YT 300] [--workers 16]
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


class Certificate:
    def __init__(self, path, N, rho_e, YT):
        ctx.prec = PREC
        d = json.load(open(path))
        self.r_fr = Fraction(d["r"])
        self.r = A(self.r_fr)
        self.gauss = [(A(a), A(s), A(c), Fraction(a), Fraction(s), Fraction(c)) for a, s, c in d["gauss"]]
        for (_, _, _, af, sf, _) in self.gauss:
            assert af > 0 and sf >= 0
        self.q = [A(z) for z in d["psi"]]
        self.YT_fr = Fraction(YT)
        assert all(sf <= self.YT_fr for (_, _, _, _, sf, _) in self.gauss)
        self.pi = arb.pi()
        pi = self.pi
        # per-Gaussian constants
        self.gc = []
        for (a, s, c, _, _, _) in self.gauss:
            self.gc.append((pi * a, s, c, 2 * c * a.rsqrt(), pi / a, 2 * pi * s))
        # Gauss-Legendre nodes on [0, r]: x = r (1 + t)/2, F phi(y) = r * sum_q w_q phi(x_q) cos(2 pi x_q y)
        self.N = N
        xs, ws = [], []
        for k in range(N):
            t, w = arb.legendre_p_root(N, k, weight=True)
            xs.append(self.r * (1 + t) / 2)
            ws.append(w)
        self.xq = xs
        self.beta_q = [2 * pi * x for x in xs]
        phis = [1 - self.v_series(x, 1)[0] + self.psi_series(x, 1)[0] for x in xs]
        self.Pq = [self.r * w * p for w, p in zip(ws, phis)]
        # quadrature error bounds E_k (k = 0, 1, 2) for the k-th y-derivative, uniform for real y in [0, YT]
        rho = A(rho_e)
        Arho = (rho + 1 / rho) / 2
        beta = (self.r / 2) * (rho - 1 / rho) / 2
        Rx = (self.r / 2) * (1 + Arho)
        Mphi = arb(1)
        for (a, s, c, _, _, _) in self.gauss:
            Mphi += abs(c) * (2 * (pi * a * beta * beta).exp()
                              + 2 * a.rsqrt() * (pi * beta * beta / a).exp() * (2 * pi * s * beta).cosh())
        for k, qk in enumerate(self.q):
            Mphi += abs(qk) * Rx ** (2 * k)
        self.Mphi = Mphi
        self.Rx = Rx
        # moments int_{-r}^{r} phi t^(2k): integrand bounded by Mphi Rx^(2k) on the ellipse
        self.Ebase_mom = self.r * 8 * Mphi * rho ** (-2 * N) / (1 - 1 / rho)
        ch = (2 * pi * A(YT) * beta).cosh()
        base = self.r * 8 * Mphi * ch * rho ** (-2 * N) / (1 - 1 / rho)
        self.E = [base * (2 * pi * Rx) ** k for k in range(3)]
        self.E = [arb(0, e.upper()) for e in self.E]  # error balls [-E, E]

    # ---- elementary pieces as truncated Taylor series in t around a point or ball y0 ----
    def v_series(self, y0, L):
        Y = arb_series([y0, 1], prec=L) if L > 1 else None
        if L == 1:
            tot = arb(0)
            for (pa, s, c, c2, pia, tps) in self.gc:
                tot += c * ((-pa * (y0 - s) ** 2).exp() + (-pa * (y0 + s) ** 2).exp()) \
                       - c2 * (-pia * y0 * y0).exp() * (tps * y0).cos()
            return [tot]
        tot = arb_series([0], prec=L)
        for (pa, s, c, c2, pia, tps) in self.gc:
            u1 = Y - s
            u2 = Y + s
            tot += c * ((-pa * u1 * u1).exp() + (-pa * u2 * u2).exp()) - c2 * (-pia * Y * Y).exp() * (tps * Y).cos()
        co = tot.coeffs()
        return [co[i] if i < len(co) else arb(0) for i in range(L)]

    def psi_series(self, x0, L):
        # psi(x0 + t) = sum_k q_k (x0 + t)^(2k), coefficients of t^0..t^(L-1)
        out = [arb(0)] * L
        X = arb_series([x0, 1], prec=L) if L > 1 else None
        if L == 1:
            p = arb(0)
            x2 = x0 * x0
            for qk in reversed(self.q):
                p = p * x2 + qk
            return [p]
        X2 = X * X
        p = arb_series([0], prec=L)
        for qk in reversed(self.q):
            p = p * X2 + qk
        co = p.coeffs()
        return [co[i] if i < len(co) else arb(0) for i in range(L)]

    def Fphi_series(self, y0, L):
        # F phi(y0 + t) by quadrature: r sum_q w_q phi_q cos(beta_q (y0 + t)); returns coefficients incl. error balls
        c0 = arb(0); c1 = arb(0); c2 = arb(0)
        for P, b in zip(self.Pq, self.beta_q):
            sn, cs = (b * y0).sin_cos()
            c0 += P * cs
            if L > 1:
                c1 -= P * b * sn
            if L > 2:
                c2 -= P * b * b * cs
        out = [c0 + self.E[0]]
        if L > 1:
            out.append(c1 + self.E[1])
        if L > 2:
            out.append(c2 / 2 + self.E[2] / 2)
        return out

    def W_series(self, y0, L):
        vv = self.v_series(y0, L)
        ff = self.Fphi_series(y0, L)
        out = [1 - vv[0] + ff[0]]
        for i in range(1, L):
            out.append(-vv[i] + ff[i])
        return out

    def rho_series(self, x0, L):
        ff = self.Fphi_series(x0, L)
        pp = self.psi_series(x0, L)
        return [f - p for f, p in zip(ff, pp)]


CERT = None


def init_worker(path, N, rho_e, YT):
    global CERT
    CERT = Certificate(path, N, rho_e, YT)


def ball(lo, hi):
    return A(lo).union(A(hi))


def lower_bound_W(lo, hi):
    """Rigorous lower bound for W on [lo, hi] via W(y0) - |W'(y0)| eta - sup|W''| eta^2/2."""
    y0 = (lo + hi) / 2
    eta = A((hi - lo) / 2)
    w0, w1 = CERT.W_series(A(y0), 2)
    w2half = CERT.W_series(ball(lo, hi), 3)[2]      # = W''/2 enclosure over [lo, hi]
    lb = w0 - abs(w1) * eta - abs(w2half) * eta * eta
    return lb.lower()


def upper_bound_rho(lo, hi):
    x0 = (lo + hi) / 2
    eta = A((hi - lo) / 2)
    r0, r1 = CERT.rho_series(A(x0), 2)
    r2half = CERT.rho_series(ball(lo, hi), 3)[2]
    ub = abs(r0) + abs(r1) * eta + abs(r2half) * eta * eta
    return ub.upper()


def task_W(args):
    lo, hi, m, depth_max = args
    stack = [(lo, hi, 0)]
    worst = None
    nevals = 0
    while stack:
        a, b, dep = stack.pop()
        lb = lower_bound_W(a, b)
        nevals += 1
        if lb >= A(m):
            worst = float(lb) if worst is None else min(worst, float(lb))
            continue
        if dep >= depth_max:
            return (lo, hi, False, float(lb), nevals, (float(a), float(b)))
        mid = (a + b) / 2
        stack.append((a, mid, dep + 1))
        stack.append((mid, b, dep + 1))
    return (lo, hi, True, worst, nevals, None)


def task_rho(args):
    lo, hi, e, depth_max = args
    stack = [(lo, hi, 0)]
    worst = None
    while stack:
        a, b, dep = stack.pop()
        ub = upper_bound_rho(a, b)
        if ub <= A(e):
            worst = float(ub) if worst is None else max(worst, float(ub))
            continue
        if dep >= depth_max:
            return (lo, hi, False, float(ub))
        mid = (a + b) / 2
        stack.append((a, mid, dep + 1))
        stack.append((mid, b, dep + 1))
    return (lo, hi, True, worst)


def task_phi_n(args):
    lo, hi, n = args
    J = ball(lo, hi)
    vv = CERT.v_series(J, n + 1)
    pp = CERT.psi_series(J, n + 1)
    fac = 1
    for k in range(2, n + 1):
        fac *= k
    dn = (-vv[n] + pp[n]) * fac
    ub = (abs(dn) * A(hi - lo)).upper()
    return str(Fraction(float(ub.mid())) * Fraction(1000001, 1000000) + Fraction(1, 10**30))


def rho_power_series_bound(cert, Kmax):
    pi = cert.pi
    r = cert.r
    rr = r * r
    xs2 = [x * x for x in cert.xq]
    # Pq = r w_q phi_q, so r sum_q w_q phi_q x_q^(2k) = sum_q Pq x_q^(2k)
    pw = list(cert.Pq)
    tot = arb(0)
    fac = arb(1)            # (2k)!
    twopi2 = (2 * pi) ** 2
    pk = arb(1)             # (2 pi)^(2k)
    rk = arb(1)             # r^(2k)
    for k in range(Kmax + 1):
        if k > 0:
            fac = fac * (2 * k - 1) * (2 * k)
            pk = pk * twopi2
            rk = rk * rr
            pw = [p * x2 for p, x2 in zip(pw, xs2)]
        M2k = sum(pw, arb(0)) + arb(0, (cert.Ebase_mom * cert.Rx ** (2 * k)).upper())
        rho_k = (-1) ** k * pk * M2k / fac - (cert.q[k] if k < len(cert.q) else 0)
        tot += abs(rho_k) * rk
    # tail k > Kmax (q_k = 0 there since Kmax >= len(q))
    assert Kmax >= len(cert.q)
    t = 2 * pi * rr
    k = Kmax + 1
    term = 2 * r * cert.Mphi * t ** (2 * k) / arb.fac_ui(2 * k)
    ratio = t * t / ((2 * k + 1) * (2 * k + 2))
    assert ratio < 1
    tot += term / (1 - ratio)
    return tot


def phi_dd_integral(cert, nsub):
    """Upper bound for int_0^r |phi''(x)| dx, phi'' = -v'' + psi'', by ball evaluation on nsub subintervals."""
    tot = arb(0)
    r = cert.r_fr
    for i in range(nsub):
        a = r * i / nsub
        b = r * (i + 1) / nsub
        J = ball(a, b)
        vv = cert.v_series(J, 3)
        pp = cert.psi_series(J, 3)
        dd = 2 * (-vv[2] + pp[2])
        tot += abs(dd) * A(b - a)
    return tot


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("--m", type=str, default="1/50", help="target lower bound for inf W")
    ap.add_argument("--e", type=str, default="1/10000000", help="target upper bound for sup |rho|")
    ap.add_argument("--N", type=int, default=500)
    ap.add_argument("--rho", type=str, default="5/4")
    ap.add_argument("--YT", type=str, default="300")
    ap.add_argument("--w0", type=str, default="1/50", help="initial interval width for W")
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--depth", type=int, default=24)
    ap.add_argument("--nibp", type=int, default=6, help="number of integrations by parts in the tail bound (even)")
    ap.add_argument("--nsub", type=int, default=20000, help="subintervals for int |phi^(n)|")
    args = ap.parse_args()
    t0 = time.time()
    ctx.prec = PREC
    cert = Certificate(args.cert, args.N, args.rho, args.YT)
    r_fr = cert.r_fr
    m = Fraction(args.m)
    e = Fraction(args.e)
    YT = Fraction(args.YT)
    print(f"r = {r_fr} = {float(r_fr)}; {len(cert.gauss)} Gaussian pairs; psi degree {2*(len(cert.q)-1)}; "
          f"N = {args.N}, rho = {args.rho}, YT = {YT}", flush=True)
    print(f"quadrature error bounds E0,E1,E2 = {[e_.upper() for e_ in cert.E]}", flush=True)
    # (1) kappa
    pi = cert.pi
    r = cert.r
    kappa = (2 * r * r + (4 * pi * r * r).si() / (2 * pi)).sqrt()
    print(f"kappa = {kappa}  (< 1: {kappa < 1})", flush=True)
    assert kappa < 1
    # (2) tail y >= YT.  For even smooth phi and even n:  |int_0^r phi(x) cos(w x) dx|
    #     <= sum_{k<n} |phi^(k)(r)|/w^(k+1) + w^(-n) int_0^r |phi^(n)|   (repeated integration by parts; the odd
    #     derivatives of phi vanish at 0).  F phi = 2 int_0^r, w = 2 pi y >= 2 pi YT.
    VT = arb(0)
    YTa = A(YT)
    for (a, s, c, _, _, _) in cert.gauss:
        VT += abs(c) * ((-pi * a * (YTa - s) ** 2).exp() + (-pi * a * (YTa + s) ** 2).exp()
                        + 2 * a.rsqrt() * (-pi * YTa * YTa / a).exp())
    nI = args.nibp
    assert nI % 2 == 0
    ph = cert.v_series(r, nI + 1)
    pp = cert.psi_series(r, nI + 1)
    derivs = []
    fk = arb(1)
    for k in range(nI):
        if k > 0:
            fk = fk * k
        dk = (-ph[k] + pp[k]) * fk
        if k == 0:
            dk = dk + 1
        derivs.append(dk)
    nsub = args.nsub
    sub = [(r_fr * i / nsub, r_fr * (i + 1) / nsub, nI) for i in range(nsub)]
    In = arb(0)
    with Pool(args.workers, initializer=init_worker, initargs=(args.cert, args.N, args.rho, args.YT)) as pool:
        for val in pool.imap_unordered(task_phi_n, sub, chunksize=50):
            In += A(Fraction(val))
    om = 2 * pi * YTa
    B = arb(0)
    for k in range(nI):
        B += abs(derivs[k]) / om ** (k + 1)
    B += In / om ** nI
    tail_lb = 1 - VT - 2 * B
    print(f"tail: phi^(k)(r), k<{nI}: {[float(d) for d in derivs]}", flush=True)
    print(f"tail: int_0^r |phi^({nI})| <= {In.upper()}, VT <= {VT.upper()}, 2*B = {(2*B).upper()}", flush=True)
    print(f"tail lower bound for W on [YT, inf): {tail_lb.lower()}", flush=True)
    tail_ok = tail_lb > A(m)
    # (3) inf W on [r, YT]
    w0 = Fraction(args.w0)
    tasks = []
    a = r_fr
    while a < YT:
        b = min(a + w0, YT)
        tasks.append((a, b, m, args.depth))
        a = b
    ok_W = True
    worst = None
    nev = 0
    with Pool(args.workers, initializer=init_worker, initargs=(args.cert, args.N, args.rho, args.YT)) as pool:
        for res in pool.imap_unordered(task_W, tasks, chunksize=4):
            lo, hi, ok, val, ne, bad = res
            nev += ne
            if not ok:
                ok_W = False
                print(f"FAIL W on [{float(lo)}, {float(hi)}]: lower bound {val} at subinterval {bad}", flush=True)
            else:
                worst = val if worst is None else min(worst, val)
        print(f"W on [r, YT]: {'PROVED' if ok_W else 'NOT PROVED'} >= {float(m)}; smallest certified local bound "
              f"{worst}; {nev} interval evaluations; {time.time()-t0:.0f}s", flush=True)
    # (4) sup |rho| on [0, r] via the power series rho(x) = sum_k rho_k x^(2k):
    #     F phi(x) = sum_k (-1)^k (2 pi x)^(2k)/(2k)! M_2k,  M_2k = int_{-r}^{r} phi(t) t^(2k) dt (Gauss-Legendre with
    #     error <= r*8*Mphi*Rx^(2k) rho^(-2N)/(1-1/rho)); rho_k = (-1)^k (2 pi)^(2k) M_2k/(2k)! - q_k.
    #     Tail k > Kmax: |M_2k| <= 2 r Mphi r^(2k), so |rho_k| r^(2k) <= 2 r Mphi (2 pi r^2)^(2k)/(2k)!.
    sup_rho = rho_power_series_bound(cert, Kmax=60)
    ok_rho = sup_rho < A(e)
    print(f"sup|rho| on [0, r] <= {sup_rho.upper()}  (target {float(e)}: {'PROVED' if ok_rho else 'NOT PROVED'})",
          flush=True)
    # (5) final inequality m > 2 r e / (1 - kappa)
    rhs = 2 * r * A(e) / (1 - kappa)
    final_ok = A(m) > rhs
    print(f"final: m = {float(m)} > 2 r e/(1-kappa) = {rhs.upper()}: {final_ok}", flush=True)
    allok = ok_W and ok_rho and tail_ok and final_ok and (kappa < 1)
    print("RESULT:", "PASS" if allok else "FAIL",
          f"=> A_+(1) > {r_fr} and C_6.11 > {r_fr**2} = {float(r_fr**2)}" if allok else "", flush=True)
    print(f"total time {time.time()-t0:.0f}s")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
