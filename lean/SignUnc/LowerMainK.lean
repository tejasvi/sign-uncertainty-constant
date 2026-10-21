import SignUnc.LowFinal
import SignUnc.LowShardsK

/-!
# The lower bound, kernel track

`lower_weakK`: `0.5502² ≤ A₊(1)²` and `0.5502² ≤ C_{6.11}` (no hypotheses).  The certificate checks run by
`decide +kernel` (shards `SignUnc.LowShardsK`, standard axioms only).
-/

namespace SignUnc

open SignUnc.LowData

theorem lower_weakK : LowerStatementWeak := lower_weak_of lowSegs lowBase_okK lowSegs_okK

/-- The strict lower bound under `ExtremizerHyp`, kernel track. -/
theorem lower_strictK (hE : ExtremizerHyp) :
    ENNReal.ofReal ((2751 / 5000 : ℝ) ^ 2) < Aplus2 ∧ ENNReal.ofReal ((2751 / 5000 : ℝ) ^ 2) < C611 :=
  lower_strict_of lowSegs lowBase_okK lowSegs_okK hE

end SignUnc
