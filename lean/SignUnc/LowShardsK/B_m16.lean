import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem km16 : lowP.map (pieceMoms 128 16 135) = MomsLit16 := by decide +kernel

end SignUnc.LowData
