import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_117 : segOK4 cfgK upperGroups (⟨(512998929623240969698813037326945484800 : Int), 12, [⟨0, 20, 7, true⟩, ⟨0, 16, 3, true⟩, ⟨0, 14, 1, true⟩, ⟨2, 12, 0, true⟩, ⟨3, 11, 0, true⟩, ⟨36, 88, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
