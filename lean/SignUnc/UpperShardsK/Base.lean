import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem baseK : baseOK4 cfgK (flatOfGroups upperGroups) segsK = true := by decide +kernel

end SignUnc.UpperRunK
