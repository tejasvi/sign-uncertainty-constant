import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem ktail : ltailOK lowCfg lowGroups lowCos lowP = true := by decide +kernel

end SignUnc.LowData
