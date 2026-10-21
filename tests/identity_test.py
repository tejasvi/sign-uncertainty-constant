# Float64 sanity check (not rigorous) of the identity (3.2):
#   g(0) = int_O g W + sum_k d_k g(beta_k) + int_I g rho
# for self-dual test functions g with no sign conditions (Hermite functions h_{4n}, sums b + bhat).
# W, rho are built from the certificate exactly as in Definition 3.1 of the paper.
# Usage: python -I identity_test.py CERT.json
import json, sys
import numpy as np
from fractions import Fraction as Fr
from numpy.polynomial.legendre import leggauss
from numpy.polynomial.hermite import hermval

d = json.load(open(sys.argv[1]))
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

def composite(lo, hi, npan, nodes):
    t, w = leggauss(nodes)
    e = np.linspace(lo, hi, npan + 1)
    xs = np.concatenate([a + (b - a)*(t + 1)/2 for a, b in zip(e[:-1], e[1:])])
    ws = np.concatenate([(b - a)/2*w for a, b in zip(e[:-1], e[1:])])
    return xs, ws

xi, wi = composite(0.0, r, 64, 30)                 # inner nodes on [0, r]
phi = 1 - v(xi) + psi(xi)
def Fphi(y):
    y = np.atleast_1d(y); out = np.empty(len(y))
    for i in range(0, len(y), 4000):
        out[i:i+4000] = 2*np.cos(2*np.pi*np.outer(y[i:i+4000], xi)) @ (wi*phi)
    return out
yo1, wo1 = composite(r, r + 0.05, 50, 30)
yo2, wo2 = composite(r + 0.05, 14.0, 2400, 30)
yo = np.concatenate([yo1, yo2]); wo = np.concatenate([wo1, wo2])
W = 1 - v(yo) + Fphi(yo)
rho = Fphi(xi) - psi(xi)

tests = []
for n in (0, 4, 8, 12):
    c = np.zeros(n + 1); c[n] = 1
    tests.append((f"h_{n}", lambda x, c=c: hermval(np.sqrt(2*np.pi)*np.asarray(x, float), c)*np.exp(-np.pi*np.asarray(x, float)**2)))
for a, s in ((1.0, 0.0), (2.0, 0.7), (0.5, 1.3), (4.0, 2.2)):
    def g(x, a=a, s=s):
        x = np.asarray(x, float)
        return (np.exp(-np.pi*a*(x-s)**2) + np.exp(-np.pi*a*(x+s)**2)
                + 2/np.sqrt(a)*np.exp(-np.pi*x*x/a)*np.cos(2*np.pi*s*x))
    tests.append((f"b+bhat(a={a},s={s})", g))
worst = 0.0
for name, g in tests:
    g0 = float(g(np.array([0.0]))[0])
    outer = 2*np.sum(wo*g(yo)*W)
    inner = 2*np.sum(wi*g(xi)*rho)
    pm = sum(x*float(g(np.array([b]))[0]) for b, x in PM)
    tot = outer + pm + inner
    scale = 2*np.sum(wo*np.abs(g(yo)*W)) + abs(pm) + 2*np.sum(wi*np.abs(g(xi)*rho)) + abs(g0)
    rel = abs(tot - g0)/scale
    worst = max(worst, rel)
    print(f"{name:20s} g(0) = {g0: .12f}  rhs = {tot: .12f}  (cosine part {pm: .4e})  diff/scale = {rel:.1e}", flush=True)
print(f"largest relative discrepancy: {worst:.1e}")
