import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_360 : segOK4 cfgK upperGroups (⟨(1291926535153201671220443974651227406336 : Int), 16, [⟨3, 29, 0, false⟩, ⟨7, 25, 0, true⟩, ⟨9, 23, 0, true⟩, ⟨11, 21, 0, true⟩, ⟨12, 20, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
