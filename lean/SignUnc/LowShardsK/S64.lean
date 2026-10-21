import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem ks_64 : lsegM lowCfg lowGroups lowCos lowP lseg64 (momsFor 16 45) = true := by
  decide +kernel

end SignUnc.LowData
