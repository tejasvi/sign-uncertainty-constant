# Direct highspy LP solve: max t s.t. W0 + A c >= t, bounds on c; optional extra rows (G c <= h). IPM without crossover.
import numpy as np, highspy, time
from scipy.sparse import csc_matrix

def solve_maxmin(W0, A, lb, ub, extra_rows=None, extra_rhs=None, crossover=False, threads=1, time_limit=3600):
    m = A.shape[1]
    nrow = A.shape[0]
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('solver', 'ipm')
    h.setOptionValue('run_crossover', 'on' if crossover else 'off')
    h.setOptionValue('threads', threads)
    h.setOptionValue('time_limit', float(time_limit))
    lp = highspy.HighsLp()
    lp.num_col_ = m + 1
    M = np.hstack([-A, np.ones((nrow, 1))])
    rl = np.full(nrow, -highspy.kHighsInf); ru = W0.copy()
    if extra_rows is not None:
        M = np.vstack([M, np.hstack([extra_rows, np.zeros((extra_rows.shape[0], 1))])])
        rl = np.concatenate([rl, np.full(extra_rows.shape[0], -highspy.kHighsInf)])
        ru = np.concatenate([ru, extra_rhs])
    lp.num_row_ = M.shape[0]
    lp.col_cost_ = np.concatenate([np.zeros(m), [-1.0]])
    lp.col_lower_ = np.concatenate([lb, [-highspy.kHighsInf]])
    lp.col_upper_ = np.concatenate([ub, [highspy.kHighsInf]])
    lp.row_lower_ = rl; lp.row_upper_ = ru
    S = csc_matrix(M)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = S.indptr.astype(np.int32)
    lp.a_matrix_.index_ = S.indices.astype(np.int32)
    lp.a_matrix_.value_ = S.data
    lp.a_matrix_.num_col_ = m + 1
    lp.a_matrix_.num_row_ = M.shape[0]
    h.passModel(lp)
    h.run()
    st = h.getModelStatus()
    sol = h.getSolution()
    x = np.array(sol.col_value)
    if len(x) != m + 1:
        return None, str(h.modelStatusToString(st))
    # report the true max-min value of the returned c (IPM without crossover is approximate)
    c = x[:m]
    t_true = float(np.min(W0 + A @ c))
    return t_true, c, str(h.modelStatusToString(st))

if __name__ == "__main__":
    from lp_cg import Problem
    r = 0.548
    pairs = [(w, float(s)) for s in np.arange(0.2, 30 + 1e-9, 0.2) for w in [2.0, 8.0, 32.0]]
    P = Problem(r, pairs)
    grid = np.unique(np.concatenate([[r], r + np.geomspace(1e-6, 0.05, 100), np.arange(r + 0.05, 36, 0.01),
                                     np.arange(36, 80, 0.1), np.arange(80, 1500, 1.0)]))
    W0, A = P.rows(grid)
    for cross in (False, True):
        t0 = time.time()
        res = solve_maxmin(W0, A, np.full(A.shape[1], -1000.0), np.full(A.shape[1], 1000.0), crossover=cross)
        print("crossover", cross, "t =", res[0], res[-1], f"{time.time()-t0:.1f}s", flush=True)
