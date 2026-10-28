#!/usr/bin/env python3
"""Floating-point data for the figure of the paper (not part of the proof): g of Section 5 on [0, 1.5] and W of Section 4 on
[r, 12], from the certificate files. Standard library only. W uses Definition 3.1 with phi-hat computed by N-point
Gauss-Legendre quadrature on [0, r] (nodes by Newton's method), g uses Lemma 5.1.
usage, from the root of the archive:
  python3 -I paper/fig_data.py certs/cert_r05502_K35.json certs/pcert_r05509_NR2.json paper/fig_g.dat paper/fig_W.dat"""
import json, math, sys
from fractions import Fraction as Fr

low, up, out_g, out_w = sys.argv[1:5]
PI = math.pi


def legendre_nodes(n):
    xs, ws = [], []
    for i in range(1, n + 1):
        x = math.cos(PI * (i - 0.25) / (n + 0.5))
        for _ in range(100):
            p0, p1 = 1.0, x
            for k in range(2, n + 1):
                p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
            dp = n * (x * p1 - p0) / (x * x - 1)
            dx = p1 / dp
            x -= dx
            if abs(dx) < 1e-16:
                break
        xs.append(x); ws.append(2 / ((1 - x * x) * dp * dp))
    return xs, ws


# ---- W for the lower-bound certificate ----
d = json.load(open(low))
r = float(Fr(d["r"]))
G = [(float(Fr(e[0])), float(Fr(e[1])), float(Fr(e[2]))) for e in d["gauss"]]
PM = [(float(Fr(b)), float(Fr(x))) for b, x in d.get("pm", [])]
Q = [float(Fr(q)) for q in d["psi"]]


def v(z):
    o = 0.0
    for a, s, c in G:
        o += c * (math.exp(-PI * a * (z - s) ** 2) + math.exp(-PI * a * (z + s) ** 2)
                  - 2 / math.sqrt(a) * math.exp(-PI * z * z / a) * math.cos(2 * PI * s * z))
    for b, x in PM:
        o += x * math.cos(2 * PI * b * z)
    return o


def psi(z):
    return sum(q * z ** (2 * k) for k, q in enumerate(Q))


t, w = legendre_nodes(800)
X = [0.5 * r * (ti + 1) for ti in t]; WX = [0.5 * r * wi for wi in w]
PHI = [WX[i] * (1 - v(X[i]) + psi(X[i])) for i in range(len(X))]


def W(y):
    return 1 - v(y) + 2 * sum(PHI[i] * math.cos(2 * PI * y * X[i]) for i in range(len(X)))


with open(out_w, "w") as fh:
    fh.write("y W\n")
    n = 0
    y = r + 1e-6
    while y <= 12.0001:
        fh.write("%.4f %.4e\n" % (y, W(y))); n += 1
        y += 0.005
print("W points", n)

# ---- g for the upper-bound certificate ----
e = json.load(open(up))
GU = [(float(Fr(x[0])), float(Fr(x[1])), float(Fr(x[2]))) for x in e["gauss"]]


def g(y):
    o = 0.0
    for a, s, c in GU:
        o += c * (math.exp(-PI * a * (y - s) ** 2) + math.exp(-PI * a * (y + s) ** 2)
                  + 2 / math.sqrt(a) * math.exp(-PI * y * y / a) * math.cos(2 * PI * s * y))
    return o


with open(out_g, "w") as fh:
    fh.write("y g\n")
    k = 0
    for i in range(0, 751):
        y = i / 500
        fh.write("%.3f %.4e\n" % (y, g(y))); k += 1
print("g points", k)
