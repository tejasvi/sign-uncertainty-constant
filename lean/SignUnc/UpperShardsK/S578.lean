import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_578 : segOK4 cfgK upperGroups (⟨(3631367807734653607531144400744633860096 : Int), 12, [⟨28, 57, 0, false⟩, ⟨32, 53, 0, false⟩, ⟨34, 51, 0, false⟩, ⟨36, 49, 0, false⟩, ⟨37, 48, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(10633823966279326983230456482242756608, 6)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
