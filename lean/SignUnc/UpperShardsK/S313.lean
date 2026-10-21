import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_313 : segOK4 cfgK upperGroups (⟨(1106499229741205906950362889742119337984 : Int), 12, [⟨1, 27, 0, true⟩, ⟨5, 23, 0, true⟩, ⟨7, 21, 0, true⟩, ⟨9, 19, 0, true⟩, ⟨10, 18, 0, true⟩, ⟨123, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(664613997892457936451903530140172288, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
