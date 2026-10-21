import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem ks_93 : lsegM lowCfg lowGroups lowCos lowP lseg93 (momsFor 16 51) = true := by
  decide +kernel

end SignUnc.LowData
