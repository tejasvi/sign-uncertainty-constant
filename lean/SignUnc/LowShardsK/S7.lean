import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem ks_7 : lsegM lowCfg lowGroups lowCos lowP lseg7 (momsFor 20 25) = true := by
  decide +kernel

end SignUnc.LowData
