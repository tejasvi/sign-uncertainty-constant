import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_94 : segOK4 cfgK upperGroups (⟨(425934495899328980023613674878582915072 : Int), 14, [⟨0, 19, 8, true⟩, ⟨0, 15, 4, true⟩, ⟨0, 13, 2, true⟩, ⟨1, 11, 0, true⟩, ⟨2, 10, 0, true⟩, ⟨23, 75, 0, true⟩, ⟨56, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(664613997892457936451903530140172288, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
