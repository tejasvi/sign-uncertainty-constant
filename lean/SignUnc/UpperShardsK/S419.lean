import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_419 : segOK4 cfgK upperGroups (⟨(1499286102495648547393437876054961160192 : Int), 16, [⟨5, 31, 0, false⟩, ⟨9, 27, 0, true⟩, ⟨11, 25, 0, true⟩, ⟨13, 23, 0, true⟩, ⟨14, 22, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
