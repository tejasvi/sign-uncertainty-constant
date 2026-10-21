import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem ks_110 : lsegM lowCfg lowGroups lowCos lowP lseg110 (momsFor 16 110) = true := by
  decide +kernel

end SignUnc.LowData
