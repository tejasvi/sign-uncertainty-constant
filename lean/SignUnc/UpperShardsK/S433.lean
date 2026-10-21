import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_433 : segOK4 cfgK upperGroups (⟨(1547138310343905518817974930225053564928 : Int), 16, [⟨6, 32, 0, false⟩, ⟨10, 28, 0, true⟩, ⟨12, 26, 0, true⟩, ⟨14, 24, 0, true⟩, ⟨15, 23, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
