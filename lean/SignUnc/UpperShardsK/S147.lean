import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_147 : segOK4 cfgK upperGroups (⟨(643263273210162725243386129234419253248 : Int), 12, [⟨0, 21, 6, true⟩, ⟨0, 17, 2, true⟩, ⟨1, 15, 0, true⟩, ⟨3, 13, 0, true⟩, ⟨4, 12, 0, true⟩, ⟨48, 100, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
