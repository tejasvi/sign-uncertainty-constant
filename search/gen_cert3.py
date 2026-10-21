# Exact-rational certificate from an LP solution with Gaussian pairs (optionally s-derivatives k) and point-mass/cos pairs.
import numpy as np, json, sys
from fractions import Fraction as Fr
from numpy.polynomial.legendre import leggauss
import mpmath as mp

def rat(x, den):
    return Fr(int(round(x*den)), den)

def gpair_k(z, a, s, k):
    # d^k/ds^k [exp(-pi a (z-s)^2) + exp(-pi a (z+s)^2)] - d^k/ds^k [2 a^-1/2 exp(-pi z^2/a) cos(2 pi s z)]
    u1 = z - s; u2 = z + s
    G1 = np.exp(-np.pi*a*u1**2); G2 = np.exp(-np.pi*a*u2**2)
    if k == 0:
        b = G1 + G2
    elif k == 1:
        b = 2*np.pi*a*u1*G1 - 2*np.pi*a*u2*G2
    elif k == 2:
        b = (4*np.pi**2*a**2*u1**2 - 2*np.pi*a)*G1 + (4*np.pi**2*a**2*u2**2 - 2*np.pi*a)*G2
    else:
        raise ValueError
    bh = 2/np.sqrt(a)*np.exp(-np.pi*z**2/a)*(2*np.pi*z)**k*np.cos(2*np.pi*s*z + k*np.pi/2)
    return b - bh

def main(src, out, r_str, cden=10**8, D=20, n=220):
    d = json.load(open(src))
    r = Fr(r_str); rf = float(r)
    assert abs(rf - d["r"]) < 1e-12, (rf, d["r"])
    pairs = [tuple(p) if len(p) == 3 else (p[0], p[1], 0) for p in d["pairs"]]
    betas = d.get("betas", [])
    c = d["c"]
    trip = []
    for (a, s, k), cc in zip(pairs, c[:len(pairs)]):
        A = Fr(a).limit_denominator(1000); S = rat(s, 10**6); C = rat(cc, cden)
        if C != 0:
            trip.append((A, S, C, int(k)))
    pm = []
    for b, dd in zip(betas, c[len(pairs):]):
        B = rat(b, 10**7); Dd = rat(max(dd, 0.0), cden)
        assert B >= r
        if Dd > 0:
            pm.append((B, Dd))
    t, w = leggauss(n); x = 0.5*rf*(t+1); wx = 0.5*rf*w
    def v(z):
        z = np.asarray(z, float); o = np.zeros_like(z)
        for A, S, C, k in trip:
            o += float(C)*gpair_k(z, float(A), float(S), k)
        for B, Dd in pm:
            o += float(Dd)*np.cos(2*np.pi*float(B)*z)
        return o
    K = 2*np.cos(2*np.pi*np.outer(x, x))*wx[None, :]
    phi = np.linalg.solve(np.eye(n) - K, 1 - v(x))
    Q = []
    for kk in range(D+1):
        M2k = 2*np.sum(wx*phi*x**(2*kk))
        qk = (-1)**kk*(2*np.pi)**(2*kk)/float(mp.factorial(2*kk))*M2k
        if qk == 0:
            Q.append(Fr(0)); continue
        e = int(np.floor(np.log10(abs(qk))))
        Q.append(Fr(int(round(qk*10**max(0, 16 - e))), 10**max(0, 16 - e)))
    cert = {"problem": "sign uncertainty +1, d=1: certificate that A_+(1) > r",
            "r": str(r),
            "gauss": [[str(A), str(S), str(C), k] for A, S, C, k in trip],
            "pm": [[str(B), str(Dd)] for B, Dd in pm],
            "psi": [str(qq) for qq in Q],
            "conventions": "entry [a,s,c,k]: c (d/ds)^k [b - bhat], b(x)=exp(-pi a (x-s)^2)+exp(-pi a (x+s)^2), bhat(y)=2a^-1/2 exp(-pi y^2/a) cos(2 pi s y); pm [beta,d]: d (cos(2 pi beta x) - (delta_beta+delta_-beta)/2); phi=1-v_ac+psi on [-r,r]"}
    json.dump(cert, open(out, "w"), indent=0)
    t2, w2 = leggauss(1500); X2 = 0.5*rf*(t2+1); W2 = 0.5*rf*w2
    psi = lambda z: sum(float(qq)*np.asarray(z, float)**(2*kk) for kk, qq in enumerate(Q))
    phit = 1 - v(X2) + psi(X2)
    def Fphi(y):
        y = np.atleast_1d(y); res = np.empty(len(y))
        for i in range(0, len(y), 2000):
            res[i:i+2000] = 2*np.cos(2*np.pi*np.outer(y[i:i+2000], X2)) @ (W2*phit)
        return res
    xs = np.linspace(0, rf, 4001)
    rho = Fphi(xs) - psi(xs)
    sd = float(sum(Dd for _, Dd in pm))
    print(f"{len(trip)} gaussian terms, {len(pm)} pm terms (sum d = {sd:.6f}); max|rho| grid = {np.abs(rho).max():.3e}")
    ys = np.linspace(rf, 60, 300000)
    Wy = 1 - v(ys) + Fphi(ys); i = np.argmin(Wy)
    print(f"min W_ac on [r,60] grid = {Wy[i]:.6f} at {ys[i]:.5f}")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3])
