# Accurate LP for Gaussian-pair certificates: closed-form Fphi at all y (no aliasing), far-field grid, y=r included.
import numpy as np, sys, time, json
from numpy.polynomial.legendre import leggauss
from scipy.optimize import linprog
from scipy.special import wofz

def nodes(r, n):
    t, w = leggauss(n)
    return 0.5*r*(t+1), 0.5*r*w

def Gint(a, s, y, r):
    """G(s,y) = int_{-r}^{r} exp(-pi a (x-s)^2 + 2 pi i x y) dx, vectorized in y (float array)."""
    y = np.asarray(y, float)
    sa = np.sqrt(np.pi*a)
    out = np.zeros(y.shape, complex)
    for sign, u in ((+1, -r - s), (-1, r - s)):
        # term = e^{-pi y^2/a} erfc(w), w = sqrt(pi a)(u - i y/a); contributes sign * term
        w = sa*u - 1j*np.sqrt(np.pi/a)*y
        if u >= 0:
            term = np.exp(-np.pi*a*u*u + 2j*np.pi*u*y)*wofz(1j*w)
        else:
            term = 2*np.exp(-np.pi*y*y/a) - np.exp(-np.pi*a*u*u + 2j*np.pi*u*y)*wofz(-1j*w)
        out += sign*term
    # G = e^{2 pi i s y}/(2 sqrt a) * [erfc(w_-) - erfc(w_+)] * e^{-pi y^2/a}; w_- uses u=-r-s, w_+ uses u=r-s
    return np.exp(2j*np.pi*s*y)/(2*np.sqrt(a))*out

def F_b_I(a, s, y, r):     # int_I b(x) cos(2 pi x y) dx, b = Gaussian pair at +-s
    return 2*np.real(Gint(a, s, y, r))

def F_bhat_I(a, s, y, r):  # int_I bhat(x) cos(2 pi x y) dx, bhat = 2 a^{-1/2} e^{-pi x^2/a} cos(2 pi s x)
    al = 1.0/a
    return (np.real(Gint(al, 0.0, s + np.asarray(y), r)) + np.real(Gint(al, 0.0, s - np.asarray(y), r)))/np.sqrt(a)

def v_pair(z, a, s):
    return np.exp(-np.pi*a*(z-s)**2) + np.exp(-np.pi*a*(z+s)**2) - 2/np.sqrt(a)*np.exp(-np.pi*z**2/a)*np.cos(2*np.pi*s*z)

def Cmat(xq, y, r):        # int_I cos(2 pi x xq) cos(2 pi x y) dx
    Y = y[:, None]; Xq = xq[None, :]
    d = Xq - Y; s_ = Xq + Y
    t1 = np.where(np.abs(d) < 1e-12, r, np.sin(2*np.pi*r*d)/(2*np.pi*np.where(np.abs(d) < 1e-12, 1, d)))
    t2 = np.sin(2*np.pi*r*s_)/(2*np.pi*s_)
    return t1 + t2

def FI1(y, r):
    return 2*r*np.sinc(2*r*y)

def build(r, pairs, y, n=120):
    xq, wq = nodes(r, n)
    K = 2*np.cos(2*np.pi*np.outer(xq, xq))*wq[None, :]
    R = np.linalg.inv(np.eye(n) - K)
    CM = Cmat(xq, y, r)*(2*wq)[None, :]
    W0 = 1 + FI1(y, r) + CM @ (R @ np.ones(n))
    A = np.empty((len(y), len(pairs)))
    for j, (a, s) in enumerate(pairs):
        vj = v_pair(xq, a, s)
        A[:, j] = -v_pair(y, a, s) - (F_b_I(a, s, y, r) - F_bhat_I(a, s, y, r)) - CM @ (R @ vj)
    return W0, A

def make_grid(r, X, Yfar=400.0):
    g = [np.array([r]), r + np.geomspace(1e-6, 0.05, 400), np.arange(r + 0.05, X + 5, 0.002),
         np.arange(X + 5, 60, 0.01), np.arange(60, Yfar, 0.05)]
    return np.unique(np.concatenate(g))

def maxmin(W0, A, cmax):
    m = A.shape[1]
    cobj = np.zeros(m+1); cobj[-1] = -1
    Aub = np.hstack([-A, np.ones((len(W0),1))])
    res = linprog(cobj, A_ub=Aub, b_ub=W0, bounds=[(-cmax, cmax)]*m + [(None, None)], method='highs')
    return (-res.fun, res.x[:-1]) if res.status == 0 else (None, res.message)

if __name__ == "__main__":
    ds = float(sys.argv[1]); X = float(sys.argv[2]); widths = [float(w) for w in sys.argv[3].split(',')]
    cmax = float(sys.argv[4]); rs = [float(z) for z in sys.argv[5].split(',')]
    pairs = [(a, s) for s in np.arange(ds, X + 1e-9, ds) for a in widths]
    for r in rs:
        t0 = time.time()
        y = make_grid(r, X)
        W0, A = build(r, pairs, y)
        t, c = maxmin(W0, A, cmax)
        if t is None:
            print(f"r={r}: LP failed {c}", flush=True); continue
        W = W0 + A @ c; i = np.argmin(W)
        print(f"ds={ds} X={X} widths={widths} cmax={cmax} r={r}: maxmin={t:.5f} argmin={y[i]:.4f} W(r)={W[0]:.3f} |c|max={np.abs(c).max():.1f} L1={np.abs(c).sum():.0f} m={len(pairs)} ny={len(y)} ({time.time()-t0:.0f}s)", flush=True)
        json.dump({"r": r, "pairs": pairs, "c": list(c), "t": t}, open(f"g2_r{r}_ds{ds}_X{X}_w{sys.argv[3]}_c{cmax}.json", "w"))
