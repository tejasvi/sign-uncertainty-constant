# Cutting-plane LP for Gaussian-pair certificates (closed-form W at all y; constraint generation on a fine grid).
import numpy as np, sys, time, json, argparse
from scipy.optimize import linprog
from lp_g2 import nodes, F_b_I, F_bhat_I, v_pair, Cmat, FI1

EPS = 1e-3
def fd(fun, a, s, k):
    if k == 0:
        return fun(a, s)
    if k == 1:
        return (fun(a, s + EPS) - fun(a, s - EPS))/(2*EPS)
    if k == 2:
        return (fun(a, s + EPS) - 2*fun(a, s) + fun(a, s - EPS))/EPS**2
    raise ValueError

class Problem:
    def __init__(self, r, pairs, n=120, betas=()):
        self.betas = list(betas)
        self.r = r
        self.pairs = [p if len(p) == 3 else (p[0], p[1], 0) for p in pairs]
        self.xq, self.wq = nodes(r, n)
        K = 2*np.cos(2*np.pi*np.outer(self.xq, self.xq))*self.wq[None, :]
        self.R = np.linalg.inv(np.eye(n) - K)
        self.R1 = self.R @ np.ones(n)
        self.RV = np.array([self.R @ fd(lambda a_, s_: v_pair(self.xq, a_, s_), a, s, k) for (a, s, k) in self.pairs]).T
        if self.betas:
            self.RB = np.array([self.R @ np.cos(2*np.pi*b*self.xq) for b in self.betas]).T

    def rows(self, y):
        y = np.asarray(y, float)
        CM = Cmat(self.xq, y, self.r)*(2*self.wq)[None, :]
        W0 = 1 + FI1(y, self.r) + CM @ self.R1
        A = np.empty((len(y), len(self.pairs)))
        r = self.r
        for j, (a, s, k) in enumerate(self.pairs):
            A[:, j] = fd(lambda a_, s_: -v_pair(y, a_, s_) - (F_b_I(a_, s_, y, r) - F_bhat_I(a_, s_, y, r)), a, s, k)
        A -= CM @ self.RV
        if self.betas:
            B = np.empty((len(y), len(self.betas)))
            for j, b in enumerate(self.betas):
                B[:, j] = -np.cos(2*np.pi*b*y) - Cmat(np.array([b]), y, r)[:, 0]
            B -= CM @ self.RB
            A = np.hstack([A, B])
        return W0, A

    def W(self, y, c, chunk=4000):
        out = np.empty(len(y))
        for i in range(0, len(y), chunk):
            W0, A = self.rows(y[i:i+chunk])
            out[i:i+chunk] = W0 + A @ c
        return out

SCALE = None
NB = 0
DSUM = 0.9
from hsolve2 import solve_maxmin
def solve(W0, A, cmax):
    # column-scaled for the IPM (raw scaling fails on the X >= 60 problems), raw-coefficient box |c| <= cmax kept exactly
    global SCALE
    m = A.shape[1]
    S = np.abs(A).max(axis=0)
    S[S == 0] = 1.0
    As = A/S[None, :]
    lb = -cmax*S; ub = cmax*S
    G = None; hrhs = None
    if NB:
        lb[m - NB:] = 0.0
        G = np.zeros((1, m)); G[0, m - NB:] = 1.0/S[m - NB:]
        hrhs = np.array([DSUM])
    res = solve_maxmin(W0, As, lb, ub, extra_rows=G, extra_rhs=hrhs)
    if res[0] is None:
        return None, res[1]
    t, z, st = res
    return t, z/S

def local_minima(y, W, thresh):
    i = np.where((W[1:-1] <= W[:-2]) & (W[1:-1] <= W[2:]) & (W[1:-1] < thresh))[0] + 1
    out = list(i)
    if W[0] < thresh: out.append(0)
    if W[-1] < thresh: out.append(len(W)-1)
    return np.array(sorted(set(out)), int)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--r", type=float, required=True)
    ap.add_argument("--ds", type=float, default=0.2)
    ap.add_argument("--X", type=float, default=30)
    ap.add_argument("--widths", type=str, default="2,8,32")
    ap.add_argument("--s0", type=float, default=None)
    ap.add_argument("--cmax", type=float, default=1000)
    ap.add_argument("--Yfar", type=float, default=1500)
    ap.add_argument("--iters", type=int, default=8)
    ap.add_argument("--out", type=str, required=True)
    ap.add_argument("--extra", type=str, action="append", default=[], help="a:s0:s1:ds extra Gaussian pairs")
    ap.add_argument("--deriv", type=str, default="", help="comma list of widths a that also get k=1,2 s-derivatives")
    ap.add_argument("--pm", type=str, default="", help="b0:b1:db point-mass/cos pairs u_b = cos(2 pi b x) - (delta_b + delta_-b)/2")
    ap.add_argument("--pmnear", type=str, default="", help="comma list of offsets o: extra betas r + o")
    ap.add_argument("--dsum", type=float, default=0.9)
    ap.add_argument("--pmharm", type=int, default=0, help="add point-mass/cos pairs at beta = k r, k = 1..K")
    a = ap.parse_args()
    r = a.r; widths = [float(w) for w in a.widths.split(',')]
    s0 = a.ds if a.s0 is None else a.s0
    pairs = [(w, float(s)) for s in np.arange(s0, a.X + 1e-9, a.ds) for w in widths]
    for ex in a.extra:
        aa, e0, e1, ed = [float(z) for z in ex.split(':')]
        pairs += [(aa, float(round(s, 6))) for s in np.arange(e0, e1 + 1e-9, ed)]
    # drop Gaussian pairs whose bump lies deep inside I (only their tiny tail outside r would matter -> huge c)
    pairs = [p for p in pairs if p[1] + 3/np.sqrt(2*np.pi*p[0]) >= r]
    for (aa, off) in ((512.0, 0.02), (512.0, 0.0), (128.0, 0.05), (128.0, 0.02), (2048.0, 0.01), (2048.0, 0.0)):
        pairs.append((aa, float(round(r - off, 7))))
    dw = [float(z) for z in a.deriv.split(',')] if a.deriv else []
    pairs = [(p[0], p[1], 0) for p in pairs] + [(p[0], p[1], k) for p in pairs if p[0] in dw for k in (1, 2)]
    t0 = time.time()
    betas = []
    if a.pm:
        b0, b1, db = [float(z) for z in a.pm.split(':')]
        betas = [float(round(b, 6)) for b in np.arange(b0, b1 + 1e-9, db)]
    if a.pmnear:
        betas = sorted(set(betas + [float(round(r + float(o), 7)) for o in a.pmnear.split(',')]))
    if a.pmharm:
        betas = sorted(set(betas + [float(round(k*r, 9)) for k in range(1, a.pmharm + 1)]))
    NB = len(betas)
    DSUM = a.dsum
    P = Problem(r, pairs, betas=betas)
    X = a.X
    smax = max(p[1] for p in pairs)
    hc = min(0.005, 1.0/(16*smax))         # finer coarse grid (better CG convergence)
    hf = min(0.0005, 1.0/(40*smax))
    Xe = max(X, smax)
    coarse = np.unique(np.concatenate([[r], r + np.geomspace(1e-6, 0.05, 100), np.arange(r + 0.05, 8, hc),
                                       np.arange(8, Xe + 6, 0.01), np.arange(Xe + 6, Xe + 80, 0.1), np.arange(Xe + 80, a.Yfar, 1.0)]))
    fine = np.unique(np.concatenate([[r], r + np.geomspace(1e-7, 0.05, 2000), np.arange(r + 0.05, 8, hf),
                                     np.arange(8, Xe + 6, 0.0005), np.arange(Xe + 6, Xe + 80, 0.005), np.arange(Xe + 80, a.Yfar, 0.05)]))
    grid = coarse
    W0g, Ag = P.rows(grid)
    print(f"r={r} m={len(pairs)} coarse={len(grid)} fine={len(fine)} setup {time.time()-t0:.0f}s", flush=True)
    best = None
    for it in range(a.iters):
        t, c = solve(W0g, Ag, a.cmax)
        if t is None:
            print("LP failed:", c, flush=True); break
        Wf = P.W(fine, c)
        mn = Wf.min(); imn = np.argmin(Wf)
        print(f"  it {it}: LP t={t:.6f}  fine min={mn:.6f} at y={fine[imn]:.5f}  rows={len(grid)}  ({time.time()-t0:.0f}s)", flush=True)
        if best is None or mn > best[0]:
            best = (mn, c.copy(), t)
            json.dump({"r": r, "pairs": pairs, "betas": betas, "c": list(c), "t": t, "finemin": float(mn)}, open(a.out, "w"))
        if mn >= t - 2e-4:
            break
        idx = local_minima(fine, Wf, t - 1e-4)
        newy = fine[idx]
        # add the minima and their immediate neighbours
        add = np.unique(np.concatenate([newy, fine[np.clip(idx-1, 0, len(fine)-1)], fine[np.clip(idx+1, 0, len(fine)-1)]]))
        W0n, An = P.rows(add)
        grid = np.concatenate([grid, add]); W0g = np.concatenate([W0g, W0n]); Ag = np.vstack([Ag, An])
    if best is not None:
        print(f"best fine min {best[0]:.6f} (LP t {best[2]:.6f}); saved {a.out}; total {time.time()-t0:.0f}s", flush=True)
