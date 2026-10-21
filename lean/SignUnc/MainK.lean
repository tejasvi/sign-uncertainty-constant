import SignUnc.LowerMainK
import SignUnc.UpperMainK

/-!
# Theorem 1.1, kernel track

`mainK`: Theorem 1.1 under `ExtremizerHyp`, from the lower checks (`SignUnc.LowShardsK`) and the upper half
`upperK` (`SignUnc.UpperMainK`), all certificate checks by `decide +kernel` (standard axioms only).
-/

namespace SignUnc

open SignUnc.LowData

theorem mainK (hE : ExtremizerHyp) : MainStatement := main_of lowSegs lowBase_okK lowSegs_okK upperK hE

end SignUnc
