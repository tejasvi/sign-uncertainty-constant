# Ball-arithmetic value of W at the numerically located minima (program 2's closed-form W, repo copies).
# Usage: python -I wmin_eval.py REPO_CHECKER_DIR
import sys
sys.path.insert(0, sys.argv[1])
from fractions import Fraction as Fr
import indep_check_pm as P2
import indep_check as P2a
base = sys.argv[1] + "/../certs/"
cases = [("cert_r05502_K35.json", P2, "29194477/10000000"),
         ("cert_r05485_X30.json", P2a, "459725029366964/100000000000000"),
         ("cert_r0548_X30.json", P2a, "220496810525357/100000000000000")]
for name, mod, y in cases:
    C = mod.Cert(base + name)
    yy = mod.A(Fr(y))
    w = C.W(yy)
    print(f"{name}: y = {float(Fr(y)):.10f}  W(y) = {w.str(12)}  upper = {w.upper()}", flush=True)
    for dy in ("-1/1000", "1/1000"):
        y2 = Fr(y) + Fr(dy)
        print(f"   W({float(y2):.7f}) = {C.W(mod.A(y2)).str(10)}", flush=True)
