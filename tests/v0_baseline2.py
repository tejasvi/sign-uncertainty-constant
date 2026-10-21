# Float check of the certificate with v = 0 (no Gaussian pairs, no cosines):
# phi = (I - K)^{-1} 1 on I = [-r, r] (Nystrom, Gauss-Legendre), W(y) = 1 + (F phi)(y) for y > r.
# Reports min_{r < y <= 60} W(y) and the threshold r* where this minimum crosses 0.  Numerics only.
import numpy as np
from numpy.polynomial.legendre import leggauss

def setup(r, n):
    t, w = leggauss(n)
    x = 0.5 * r * (t + 1); wx = 0.5 * r * w          # nodes on [0, r]; even functions: int_I = 2 int_0^r
    K = 2 * np.cos(2 * np.pi * np.outer(x, x)) * wx[None, :]
    phi = np.linalg.solve(np.eye(n) - K, np.ones(n))
    return x, wx * phi, phi

def W(y, x, wphi):
    y = np.atleast_1d(y)
    return 1 + 2 * np.cos(2 * np.pi * np.outer(y, x)) @ wphi

def W_min(r, n=160):
    x, wphi, phi = setup(r, n)
    ys = np.concatenate([r + np.geomspace(1e-6, 0.05, 200), np.arange(r + 0.05, 60, 2e-3)])
    Ws = np.concatenate([W(ys[i:i + 5000], x, wphi) for i in range(0, len(ys), 5000)])
    j = np.argmin(Ws)
    lo, hi = ys[max(j - 1, 0)], ys[min(j + 1, len(ys) - 1)]
    for _ in range(60):                               # golden-section refinement of the grid minimum
        a = lo + 0.382 * (hi - lo); b = lo + 0.618 * (hi - lo)
        if W(a, x, wphi)[0] < W(b, x, wphi)[0]: hi = b
        else: lo = a
    y = 0.5 * (lo + hi)
    return W(y, x, wphi)[0], y, phi[-1]

for r in (0.40, 0.45, 0.453, 0.455, 0.46):
    m, y, pr = W_min(r)
    print(f"r = {r}: min W = {m:.6f} at y = {y:.4f}", flush=True)
for n in (120, 160, 240):
    lo, hi = 0.45, 0.46
    for _ in range(24):
        mid = 0.5 * (lo + hi)
        if W_min(mid, n=n)[0] > 0: lo = mid
        else: hi = mid
    print(f"n = {n}: threshold r* in [{lo:.6f}, {hi:.6f}]", flush=True)
