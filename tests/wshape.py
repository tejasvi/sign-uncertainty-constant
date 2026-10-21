# Float64 scan of W for a certificate (numerics only; used for the remark on the shape of W).
# Usage: python -I wshape.py CERT.json Ymax step thresh [ystar]
import json, sys
import numpy as np
from fractions import Fraction as Fr
from numpy.polynomial.legendre import leggauss

d = json.load(open(sys.argv[1]))
Ymax, step, thr = float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
ystar = float(sys.argv[5]) if len(sys.argv) > 5 else None
r = float(Fr(d["r"]))
G = [(float(Fr(e[0])), float(Fr(e[1])), float(Fr(e[2]))) for e in d["gauss"]]
PM = [(float(Fr(b)), float(Fr(x))) for b, x in d.get("pm", [])]
Q = [float(Fr(q)) for q in d["psi"]]

def v(z):
    z = np.asarray(z, float); o = np.zeros_like(z)
    for a, s, c in G:
        o += c * (np.exp(-np.pi*a*(z-s)**2) + np.exp(-np.pi*a*(z+s)**2) - 2/np.sqrt(a)*np.exp(-np.pi*z**2/a)*np.cos(2*np.pi*s*z))
    for b, x in PM:
        o += x * np.cos(2*np.pi*b*z)
    return o

def psi(z):
    z = np.asarray(z, float); return sum(q * z**(2*k) for k, q in enumerate(Q))

t, w = leggauss(3000); X = 0.5*r*(t+1); WX = 0.5*r*w
phiX = 1 - v(X) + psi(X)
def W(y):
    y = np.atleast_1d(np.asarray(y, float)); out = np.empty(len(y))
    for i in range(0, len(y), 2000):
        yy = y[i:i+2000]
        out[i:i+2000] = 1 - v(yy) + 2*np.cos(2*np.pi*np.outer(yy, X)) @ (WX*phiX)
    return out

at = f"; W({ystar}) = {W(ystar)[0]:.12f}" if ystar is not None else ""
print(f"r = {d['r']}{at}; W(r+1e-9) = {W(r+1e-9)[0]:.6f}", flush=True)
ys = np.arange(r + step, Ymax, step)
Ws = W(ys)
j = np.argmin(Ws)
print(f"grid [{r+step:.4f}, {Ymax}] step {step}: min W = {Ws[j]:.7f} at y = {ys[j]:.5f}", flush=True)
below = Ws < thr
# maximal runs where W < thr, merged across gaps shorter than 0.02
runs = []
i = 0
n = len(ys)
while i < n:
    if below[i]:
        k = i
        while k + 1 < n and below[k+1]:
            k += 1
        runs.append([ys[i], ys[k]])
        i = k + 1
    else:
        i += 1
merged = []
for a, b in runs:
    if merged and a - merged[-1][1] < 0.02:
        merged[-1][1] = b
    else:
        merged.append([a, b])
print(f"intervals (gaps < 0.02 merged) where W < {thr}, length >= 0.1:", flush=True)
for a, b in merged:
    if b - a >= 0.1:
        m = (ys >= a) & (ys <= b)
        frac = below[m].mean()
        print(f"  [{a:.3f}, {b:.3f}]  length {b-a:.3f}  fraction below {frac:.3f}  max W inside {Ws[m].max():.5f}", flush=True)
for (a, b) in ((1.0, 2.4), (2.3, 3.2), (3.0, 4.1), (4.0, 4.9), (4.8, 5.8), (5.6, 6.9), (6.8, 7.5)):
    m = (ys >= a) & (ys <= b)
    print(f"  on [{a}, {b}]: min {Ws[m].min():.6f}  max {Ws[m].max():.5f}", flush=True)
