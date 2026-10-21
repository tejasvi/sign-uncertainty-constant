import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_33 : segOK4 cfgK upperGroups (⟨(255793312438859748291926371162698809344 : Int), 16, [⟨0, 17, 10, true⟩, ⟨0, 13, 6, true⟩, ⟨0, 11, 4, true⟩, ⟨0, 9, 2, true⟩, ⟨0, 8, 1, true⟩, ⟨0, 50, 0, true⟩, ⟨6, 70, 0, true⟩, ⟨0, 1, 1, false⟩], [(664613997892457936451903530140172288, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
