import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem kpp_4 : ppOK 128 24 4 24 8 lowGroups lowCos lowPsi lowEps (lowPS.getD 4 ((0, 0, []), [])) = true := by
  decide +kernel

end SignUnc.LowData
