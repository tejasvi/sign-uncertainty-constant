# Exact-rational primal certificate from a primal LP solution; fixes g(0) < 0 after rounding.
import json, sys, numpy as np
from fractions import Fraction as Fr
from primal_lp import e_pair

def main(src, out, r_str, cden=10**12):
    d = json.load(open(src))
    r = Fr(r_str); assert abs(float(r) - d["r"]) < 1e-12
    terms = []
    for (a, s), c in zip(d["pairs"], d["c"]):
        A = Fr(a).limit_denominator(10**6); S = Fr(s).limit_denominator(10**6); C = Fr(int(round(c*cden)), cden)
        if C != 0:
            terms.append([A, S, C])
    # g(0) in float; push it below 0 by adjusting the (a=1, s=0) coefficient if needed (keeps positivity margin)
    g0 = sum(float(C)*e_pair(0.0, float(A), float(S)) for A, S, C in terms)
    print("g(0) after rounding (float):", g0)
    if g0 > -1e-9:
        idx = [i for i, (A, S, C) in enumerate(terms) if A == 1 and S == 0]
        delta = Fr(int((g0 + 1e-8)*cden) + 1, cden) / 4      # e_{1,0}(0) = 4
        if idx:
            terms[idx[0]][2] -= delta
        else:
            terms.append([Fr(1), Fr(0), -delta])
        print("adjusted (1,0) coefficient by", float(-delta))
    json.dump({"problem": "sign uncertainty +1, d=1: self-dual g with g(0) < 0 and g >= 0 on |x| >= r (upper bound)",
               "r": str(r), "gauss": [[str(A), str(S), str(C)] for A, S, C in terms],
               "conventions": "g = sum c (b + bhat), b(x)=exp(-pi a (x-s)^2)+exp(-pi a (x+s)^2), bhat(x)=2a^-1/2 exp(-pi x^2/a) cos(2 pi s x)"},
              open(out, "w"), indent=0)
    ys = np.linspace(float(r), max(float(S) for _, S, _ in terms) + 15, 400000)
    g = sum(float(C)*e_pair(ys, float(A), float(S)) for A, S, C in terms)
    k = np.argmin(g)
    print(f"{len(terms)} terms; float min g on [r, X+15] = {g[k]:.4e} at {ys[k]:.5f}; g(0) = {sum(float(C)*e_pair(0.0, float(A), float(S)) for A, S, C in terms):.4e}")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3])
