# PRIMAL (upper-bound) LP, robust version: g = sum c_j (b_j + bhat_j) + c_T e_{A,0} (tail term, A > all widths).
# maximize eps s.t. g(y) >= eps * w(y) on a grid of [r, Y] (w = tail envelope), g(0) = -1, c_T >= cT_min, |c| <= cmax.
import numpy as np, sys, time, argparse, json
import highspy
from scipy.sparse import csc_matrix
from primal_lp import e_pair

def solve(M, g0, w, cmax, iT, cTmin):
    nrow, m = M.shape
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    h.setOptionValue('solver', 'ipm'); h.setOptionValue('run_crossover', 'off')
    lp = highspy.HighsLp(); lp.num_col_ = m + 1
    A = np.vstack([np.hstack([M, -w[:, None]]), np.hstack([g0, [0.0]])[None, :]])
    lp.num_row_ = A.shape[0]
    lp.col_cost_ = np.concatenate([np.zeros(m), [-1.0]])
    lo = np.full(m, -cmax); hi = np.full(m, cmax); lo[iT] = 0.0; hi[iT] = cmax     # box normalisation |c| <= cmax
    lp.col_lower_ = np.concatenate([lo, [-highspy.kHighsInf]]); lp.col_upper_ = np.concatenate([hi, [highspy.kHighsInf]])
    lp.row_lower_ = np.concatenate([np.zeros(nrow), [-highspy.kHighsInf]])
    lp.row_upper_ = np.concatenate([np.full(nrow, highspy.kHighsInf), [0.0]])
    S = csc_matrix(A)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = S.indptr.astype(np.int32); lp.a_matrix_.index_ = S.indices.astype(np.int32)
    lp.a_matrix_.value_ = S.data; lp.a_matrix_.num_col_ = m + 1; lp.a_matrix_.num_row_ = A.shape[0]
    h.passModel(lp); h.run()
    x = np.array(h.getSolution().col_value)
    if len(x) != m + 1:
        return None, None, h.modelStatusToString(h.getModelStatus())
    c = x[:m]
    return float(np.min((M @ c)/w)), c, h.modelStatusToString(h.getModelStatus())

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--X", type=float, default=25); ap.add_argument("--ds", type=float, default=0.2)
    ap.add_argument("--widths", type=str, default="1,2,4,8,16"); ap.add_argument("--A", type=float, default=64)
    ap.add_argument("--cmax", type=float, default=1e5); ap.add_argument("--cTmin", type=float, default=1e-6)
    ap.add_argument("--rs", type=str, default="0.553,0.552"); ap.add_argument("--hy", type=float, default=0.001)
    ap.add_argument("--iters", type=int, default=6); ap.add_argument("--out", type=str, default="")
    a = ap.parse_args()
    widths = [float(x) for x in a.widths.split(',')]
    # tail term: wide Gaussian pair (a_T = 1/A) centred at s_T = X; it dominates for y -> infinity; c_T = 1 fixes the scale
    pairs = [(wd, float(round(s, 6))) for s in np.arange(0.0, a.X + 1e-9, a.ds) for wd in widths] + [(1.0/a.A, float(a.X))]
    iT = len(pairs) - 1
    W = lambda y: np.exp(-np.pi*np.maximum(0.0, np.asarray(y) - a.X)**2/a.A)
    def cols(y):
        Mx = np.empty((len(y), len(pairs)))
        for j, (aa, s) in enumerate(pairs):
            Mx[:, j] = e_pair(y, aa, s)
        return Mx
    g0 = np.array([e_pair(0.0, aa, s) for (aa, s) in pairs])
    for r in [float(z) for z in a.rs.split(',')]:
        t0 = time.time()
        Y = a.X + 3*np.sqrt(a.A) + 6
        y = np.unique(np.concatenate([np.arange(r, a.X + 6, a.hy), np.arange(a.X + 6, Y, 0.01)]))
        M = cols(y); w = W(y)
        yf = np.unique(np.concatenate([np.arange(r, a.X + 6, a.hy/8), np.arange(a.X + 6, Y, 0.002)]))
        best = None
        for it in range(a.iters):
            eps, c, st = solve(M, g0, w, a.cmax, iT, a.cTmin)
            if c is None:
                print(f"r={r} it {it}: {st}", flush=True); break
            gf = cols(yf) @ c; rel = gf/W(yf); k = np.argmin(rel)
            print(f"r={r} it {it}: eps={eps:.4e} ({st}) fine min g/w {rel[k]:.4e} at {yf[k]:.5f}; cT={c[iT]:.3e} L1={np.abs(c).sum():.4g} rows={len(y)} ({time.time()-t0:.0f}s)", flush=True)
            if best is None or rel[k] > best[0]:
                best = (rel[k], c.copy(), eps)
            if rel[k] >= 0.9*eps:
                break
            # add local minima of the fine relative margin
            idx = np.where((rel[1:-1] <= rel[:-2]) & (rel[1:-1] <= rel[2:]) & (rel[1:-1] < eps))[0] + 1
            add = yf[idx]
            M = np.vstack([M, cols(add)]); w = np.concatenate([w, W(add)]); y = np.concatenate([y, add])
        if a.out and best is not None:
            json.dump({"r": r, "pairs": pairs, "c": list(best[1]), "finemin_rel": float(best[0]), "eps": float(best[2]), "A": a.A},
                      open(a.out.replace('.json', f'_r{r}.json'), 'w'))
