import SignUnc.MainK
import SignUnc.Lower.ExtremizerProbe

/-! The probe of `ExtremizerHyp` with the proved bounds (kernel track): `0 < A₊(1)² < ⊤`. -/

namespace SignUnc

theorem aplus2_pos_finiteK : 0 < Aplus2 ∧ Aplus2 < ⊤ := probe_bounds lower_weakK upperK

end SignUnc
