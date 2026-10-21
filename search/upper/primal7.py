# PRIMAL LP, sparse version for long ranges: g = sum c_j (b_j + bhat_j) + c_T * tail pair (a = 1/A at s = X).
# maximize eps s.t. g(y) >= eps * w(y) on grid [r, Y], g(0) <= 0, |c| <= 1 (box normalisation), c_T >= 0.
import numpy as np, sys, time, argparse, json
import highspy
from scipy.sparse import csc_matrix, coo_matrix, vstack as svstack, hstack as shstack

def e_pair(z, a, s):
    z = np.asarray(z, float)
    return (np.exp(-np.pi*a*(z-s)**2) + np.exp(-np.pi*a*(z+s)**2)
            + 2/np.sqrt(a)*np.exp(-np.pi*z**2/a)*np.cos(2*np.pi*s*z))

def sparse_cols(y, pairs, tol=1e-17):
    rows, cols, vals = [], [], []
    for j, (a, s) in enumerate(pairs):
        v = e_pair(y, a, s)
        mx = np.abs(v).max()
        k = np.nonzero(np.abs(v) > tol*max(mx, 1e-300))[0]
        rows.append(k); cols.append(np.full(len(k), j)); vals.append(v[k])
    return coo_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(len(y), len(pairs))).tocsc()

def solve(M, g0, w, iT, cmax):
    nrow, m = M.shape
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    h.setOptionValue('solver', 'ipm'); h.setOptionValue('run_crossover', 'off')
    A = svstack([shstack([M, csc_matrix(-w[:, None])]), csc_matrix(np.concatenate([g0, [0.0]])[None, :])]).tocsc()
    lp = highspy.HighsLp(); lp.num_col_ = m + 1; lp.num_row_ = A.shape[0]
    lp.col_cost_ = np.concatenate([np.zeros(m), [-1.0]])
    lo = np.full(m, -cmax); hi = np.full(m, cmax); lo[iT] = 0.0
    lp.col_lower_ = np.concatenate([lo, [-highspy.kHighsInf]]); lp.col_upper_ = np.concatenate([hi, [highspy.kHighsInf]])
    lp.row_lower_ = np.concatenate([np.zeros(nrow), [-highspy.kHighsInf]])
    lp.row_upper_ = np.concatenate([np.full(nrow, highspy.kHighsInf), [0.0]])
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = A.indptr.astype(np.int32); lp.a_matrix_.index_ = A.indices.astype(np.int32)
    lp.a_matrix_.value_ = A.data; lp.a_matrix_.num_col_ = m + 1; lp.a_matrix_.num_row_ = A.shape[0]
    h.passModel(lp); h.run()
    x = np.array(h.getSolution().col_value)
    st = h.modelStatusToString(h.getModelStatus())
    if len(x) != m + 1:
        return None, None, st
    return float(np.min((M @ x[:m])/w)), x[:m], st

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--X", type=float, default=120); ap.add_argument("--ds", type=float, default=0.25)
    ap.add_argument("--widths", type=str, default="1,2,4,8,16"); ap.add_argument("--A", type=float, default=64)
    ap.add_argument("--rs", type=str, default="0.5508"); ap.add_argument("--hy", type=float, default=0.001)
    ap.add_argument("--iters", type=int, default=5); ap.add_argument("--out", type=str, default="")
    ap.add_argument("--extra", type=str, action="append", default=[], help="a:s0:s1:ds extra Gaussian pairs")
    a = ap.parse_args()
    widths = [float(x) for x in a.widths.split(',')]
    pairs = [(wd, float(round(s, 6))) for s in np.arange(0.0, a.X + 1e-9, a.ds) for wd in widths]
    for ex in a.extra:
        aa, e0, e1, ed = [float(z) for z in ex.split(':')]
        pairs += [(aa, float(round(s, 6))) for s in np.arange(e0, e1 + 1e-9, ed)]
    pairs += [(1.0/a.A, float(a.X))]
    iT = len(pairs) - 1
    W = lambda y: np.exp(-np.pi*np.maximum(0.0, np.asarray(y) - a.X)**2/a.A)
    g0 = np.array([e_pair(0.0, aa, s) for (aa, s) in pairs])
    for r in [float(z) for z in a.rs.split(',')]:
        t0 = time.time()
        Y = a.X + 3*np.sqrt(a.A) + 6
        y = np.unique(np.concatenate([np.arange(r, a.X + 6, a.hy), np.arange(a.X + 6, Y, 0.01)]))
        M = sparse_cols(y, pairs); w = W(y)
        print(f"r={r}: m={len(pairs)} rows={len(y)} nnz={M.nnz} ({time.time()-t0:.0f}s)", flush=True)
        best = None
        for it in range(a.iters):
            eps, c, st = solve(M, g0, w, iT, 1.0)
            if c is None:
                print(f"r={r} it {it}: {st}", flush=True); break
            # fine check in chunks
            yf = np.unique(np.concatenate([np.arange(r, a.X + 6, a.hy/8), np.arange(a.X + 6, Y, 0.002)]))
            rel = np.empty(len(yf))
            for i0 in range(0, len(yf), 200000):
                yy = yf[i0:i0+200000]
                rel[i0:i0+200000] = (sparse_cols(yy, pairs) @ c)/W(yy)
            k = np.argmin(rel)
            print(f"r={r} it {it}: eps={eps:.4e} ({st}) fine min g/w {rel[k]:.4e} at {yf[k]:.5f}; cT={c[iT]:.3e} L1={np.abs(c).sum():.4g} ({time.time()-t0:.0f}s)", flush=True)
            if best is None or rel[k] > best[0]:
                best = (rel[k], c.copy(), eps)
            if rel[k] >= 0.9*eps:
                break
            idx = np.where((rel[1:-1] <= rel[:-2]) & (rel[1:-1] <= rel[2:]) & (rel[1:-1] < eps))[0] + 1
            add = yf[idx]
            M = svstack([M, sparse_cols(add, pairs)]).tocsc(); w = np.concatenate([w, W(add)])
        if a.out and best is not None:
            json.dump({"r": r, "pairs": pairs, "c": list(best[1]), "finemin_rel": float(best[0]), "eps": float(best[2]), "A": a.A},
                      open(a.out.replace('.json', f'_r{r}.json'), 'w'))
