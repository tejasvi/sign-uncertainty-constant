# Direct highspy LP solve: max t s.t. W0 + A c >= t, bounds on c; optional extra rows (G c <= h).
# IPM without crossover; HiGHS IPM is numerically fragile here (Solve error on 1e-16 matrix perturbations),
# so retry with other settings when the status is an error.
import numpy as np, highspy
from scipy.sparse import csc_matrix

ATTEMPTS = ({'presolve': 'on'}, {'presolve': 'off'}, {'presolve': 'on', 'random_seed': 7},
            {'presolve': 'off', 'random_seed': 11}, {'solver': 'simplex', 'presolve': 'on'})

def solve_maxmin(W0, A, lb, ub, extra_rows=None, extra_rhs=None, crossover=False, threads=1, time_limit=3600):
    m = A.shape[1]
    nrow = A.shape[0]
    M = np.hstack([-A, np.ones((nrow, 1))])
    rl = np.full(nrow, -highspy.kHighsInf); ru = W0.copy()
    if extra_rows is not None:
        M = np.vstack([M, np.hstack([extra_rows, np.zeros((extra_rows.shape[0], 1))])])
        rl = np.concatenate([rl, np.full(extra_rows.shape[0], -highspy.kHighsInf)])
        ru = np.concatenate([ru, extra_rhs])
    S = csc_matrix(M)
    last = None
    for att in ATTEMPTS:
        h = highspy.Highs()
        h.setOptionValue('output_flag', False)
        h.setOptionValue('solver', 'ipm')
        h.setOptionValue('run_crossover', 'on' if crossover else 'off')
        h.setOptionValue('time_limit', float(time_limit))
        for k_, v_ in att.items():
            h.setOptionValue(k_, v_)
        lp = highspy.HighsLp()
        lp.num_col_ = m + 1
        lp.num_row_ = M.shape[0]
        lp.col_cost_ = np.concatenate([np.zeros(m), [-1.0]])
        lp.col_lower_ = np.concatenate([lb, [-highspy.kHighsInf]])
        lp.col_upper_ = np.concatenate([ub, [highspy.kHighsInf]])
        lp.row_lower_ = rl; lp.row_upper_ = ru
        lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
        lp.a_matrix_.start_ = S.indptr.astype(np.int32)
        lp.a_matrix_.index_ = S.indices.astype(np.int32)
        lp.a_matrix_.value_ = S.data
        lp.a_matrix_.num_col_ = m + 1
        lp.a_matrix_.num_row_ = M.shape[0]
        h.passModel(lp)
        h.run()
        st = h.modelStatusToString(h.getModelStatus())
        x = np.array(h.getSolution().col_value)
        if len(x) == m + 1 and st not in ('Solve error', 'Not Set', 'Load error', 'Model error', 'Presolve error',
                                          'Postsolve error', 'Model empty'):
            c = x[:m]
            # IPM without crossover is approximate: report the true max-min value of the returned c
            return float(np.min(W0 + A @ c)), c, f"{st} ({att})"
        last = st
    return None, f"all attempts failed (last status {last})"
