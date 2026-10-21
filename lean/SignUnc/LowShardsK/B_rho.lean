import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem krho : rhoOK 128 30 lowPsi lowP lowEps lowDelta = true := by decide +kernel

end SignUnc.LowData
