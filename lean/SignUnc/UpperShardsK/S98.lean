import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_98 : segOK4 cfgK upperGroups (⟨(435903705867715849070392227830685499392 : Int), 14, [⟨0, 19, 8, true⟩, ⟨0, 15, 4, true⟩, ⟨0, 13, 2, true⟩, ⟨1, 11, 0, true⟩, ⟨2, 10, 0, true⟩, ⟨23, 75, 0, true⟩, ⟨56, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
