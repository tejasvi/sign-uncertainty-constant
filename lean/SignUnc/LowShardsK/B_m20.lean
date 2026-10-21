import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem km20 : lowP.map (pieceMoms 128 20 25) = MomsLit20 := by decide +kernel

end SignUnc.LowData
