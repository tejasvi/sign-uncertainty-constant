# PRIMAL (upper-bound) LP in a Gaussian-pair family: g = sum_j c_j (b_j + bhat_j) is self-dual.
# Feasibility for given r: g(0) = -1, g(y) >= 0 on a grid of [r, Y].  Bisection on r gives the family's primal value.
import numpy as np, sys, time, argparse
import highspy
from scipy.sparse import csc_matrix

def e_pair(z, a, s):
    z = np.asarray(z, float)
    return (np.exp(-np.pi*a*(z-s)**2) + np.exp(-np.pi*a*(z+s)**2)
            + 2/np.sqrt(a)*np.exp(-np.pi*z**2/a)*np.cos(2*np.pi*s*z))

def build(pairs, y):
    M = np.empty((len(y), len(pairs)))
    for j, (a, s) in enumerate(pairs):
        M[:, j] = e_pair(y, a, s)
    g0 = np.array([e_pair(0.0, a, s) for (a, s) in pairs])
    return M, g0

def feasible(M, g0, cmax, tmargin=0.0):
    # minimize ||c||_1 s.t. M c >= 0 (grid), g0.c = -1.  Infeasible <=> r below the family/grid primal value.
    nrow, m = M.shape
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    h.setOptionValue('solver', 'ipm'); h.setOptionValue('run_crossover', 'off')
    lp = highspy.HighsLp(); lp.num_col_ = 2*m
    A = np.vstack([np.hstack([M, -M]), np.hstack([g0, -g0])[None, :]])
    lp.num_row_ = A.shape[0]
    lp.col_cost_ = np.ones(2*m)
    lp.col_lower_ = np.zeros(2*m); lp.col_upper_ = np.full(2*m, cmax)
    lp.row_lower_ = np.concatenate([np.zeros(nrow), [-1.0]])
    lp.row_upper_ = np.concatenate([np.full(nrow, highspy.kHighsInf), [-1.0]])
    S = csc_matrix(A)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = S.indptr.astype(np.int32); lp.a_matrix_.index_ = S.indices.astype(np.int32)
    lp.a_matrix_.value_ = S.data; lp.a_matrix_.num_col_ = 2*m; lp.a_matrix_.num_row_ = A.shape[0]
    h.passModel(lp); h.run()
    st = h.modelStatusToString(h.getModelStatus())
    x = np.array(h.getSolution().col_value)
    if len(x) != 2*m:
        return None, None, st
    c = x[:m] - x[m:]
    return float(np.min(M @ c)), c, st

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--X", type=float, default=30); ap.add_argument("--ds", type=float, default=0.2)
    ap.add_argument("--widths", type=str, default="1,2,8,32"); ap.add_argument("--cmax", type=float, default=1e4)
    ap.add_argument("--rs", type=str, default="0.552,0.555,0.558,0.56")
    ap.add_argument("--hy", type=float, default=0.002)
    a = ap.parse_args()
    widths = [float(w) for w in a.widths.split(',')]
    pairs = [(w, float(s)) for s in np.arange(0.0, a.X + 1e-9, a.ds) for w in widths]
    for r in [float(z) for z in a.rs.split(',')]:
        t0 = time.time()
        Y = a.X + 12
        y = np.unique(np.concatenate([np.arange(r, Y, a.hy), np.arange(Y, Y + 30, 0.05)]))
        M, g0 = build(pairs, y)
        tmin, c, st = feasible(M, g0, a.cmax)
        if c is None:
            print(f"r={r}: {st} ({time.time()-t0:.0f}s)", flush=True); continue
        yf = np.arange(r, Y + 30, a.hy/10)
        gf = build(pairs, yf)[0] @ c
        print(f"r={r}: {st}; L1 {np.abs(c).sum():.4g}; grid min g {tmin:.3e}; fine min g {gf.min():.3e} at {yf[np.argmin(gf)]:.4f}; g(0) {g0 @ c:.4f} ({time.time()-t0:.0f}s)", flush=True)
