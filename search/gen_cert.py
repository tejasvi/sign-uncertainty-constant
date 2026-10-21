# Build an exact-rational certificate from an LP solution: r, Gaussian pairs (a, s, c), and psi (poly in x^2) ~ K phi.
import numpy as np, json, sys
from fractions import Fraction as Fr
from numpy.polynomial.legendre import leggauss
import mpmath as mp

def rat(x, den):
    return Fr(int(round(x*den)), den)

def main(src, out, r_str, cden=10**8, D=20, n=220):
    d = json.load(open(src))
    r = Fr(r_str); rf = float(r)
    assert abs(rf - d["r"]) < 1e-12, (rf, d["r"])
    trip = []
    for (a, s), c in zip(d["pairs"], d["c"]):
        A = Fr(a).limit_denominator(1000); S = rat(s, 1000); C = rat(c, cden)
        if C != 0:
            trip.append((A, S, C))
    # Nystrom with rounded data (float64)
    t, w = leggauss(n); x = 0.5*rf*(t+1); wx = 0.5*rf*w
    def v(z):
        z = np.asarray(z, float); out_ = np.zeros_like(z)
        for A, S, C in trip:
            a, s, c = float(A), float(S), float(C)
            out_ += c*(np.exp(-np.pi*a*(z-s)**2) + np.exp(-np.pi*a*(z+s)**2) - 2/np.sqrt(a)*np.exp(-np.pi*z**2/a)*np.cos(2*np.pi*s*z))
        return out_
    K = 2*np.cos(2*np.pi*np.outer(x, x))*wx[None, :]
    phi = np.linalg.solve(np.eye(n) - K, 1 - v(x))
    # psi = K phi = sum_k (-1)^k (2 pi x)^{2k}/(2k)! * M_{2k},  M_{2k} = 2 sum_p w_p phi_p x_p^{2k}
    q = []
    for k in range(D+1):
        M2k = 2*np.sum(wx*phi*x**(2*k))
        qk = (-1)**k*(2*np.pi)**(2*k)/float(mp.factorial(2*k))*M2k
        q.append(qk)
    # rationalize q with ~16 significant digits relative to |q_k|
    Q = []
    for qk in q:
        if qk == 0:
            Q.append(Fr(0)); continue
        e = int(np.floor(np.log10(abs(qk))))
        den = 10**max(0, 16 - e)
        Q.append(Fr(int(round(qk*den)), den))
    cert = {"problem": "sign uncertainty +1, d=1: certificate that A_+(1) > r",
            "r": str(r),
            "gauss": [[str(A), str(S), str(C)] for A, S, C in trip],
            "psi": [str(qq) for qq in Q],
            "conventions": "b(x)=exp(-pi a (x-s)^2)+exp(-pi a (x+s)^2); v=sum c (b - bhat); phi=1-v+psi on [-r,r], psi(x)=sum_k psi[k] x^(2k)"}
    json.dump(cert, open(out, "w"), indent=0)
    # float diagnostics: rho on a grid, W on a grid (quadrature with many nodes)
    t2, w2 = leggauss(1500); X2 = 0.5*rf*(t2+1); W2 = 0.5*rf*w2
    psi = lambda z: sum(float(qq)*np.asarray(z, float)**(2*k) for k, qq in enumerate(Q))
    phit = 1 - v(X2) + psi(X2)
    def Fphi(y):
        y = np.atleast_1d(y); res = np.empty(len(y))
        for i in range(0, len(y), 2000):
            res[i:i+2000] = 2*np.cos(2*np.pi*np.outer(y[i:i+2000], X2)) @ (W2*phit)
        return res
    xs = np.linspace(0, rf, 4001)
    rho = Fphi(xs) - psi(xs)
    print(f"{len(trip)} gaussians; max|rho| on grid = {np.abs(rho).max():.3e}; phi(r)~{1 - v(np.array([rf]))[0] + psi(rf):.4f}")
    ys = np.linspace(rf, 60, 300000)
    Wy = 1 - v(ys) + Fphi(ys)
    i = np.argmin(Wy)
    print(f"min W on [r,60] grid = {Wy[i]:.6f} at {ys[i]:.5f}; q = {[float(z) for z in Q[:4]]}...")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3])
