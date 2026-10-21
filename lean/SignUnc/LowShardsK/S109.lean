import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem ks_109 : lsegM lowCfg lowGroups lowCos lowP lseg109 (momsFor 16 107) = true := by
  decide +kernel

end SignUnc.LowData
