import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_574 : segOK4 cfgK upperGroups (⟨(3471860448240463702782687553510992510976 : Int), 12, [⟨28, 57, 0, false⟩, ⟨32, 53, 0, false⟩, ⟨34, 51, 0, false⟩, ⟨36, 49, 0, false⟩, ⟨37, 48, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 6)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
