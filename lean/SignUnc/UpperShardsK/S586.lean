import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_586 : segOK4 cfgK upperGroups (⟨(4051403854402687023368747431793222746112 : Int), 12, [⟨32, 61, 0, false⟩, ⟨36, 57, 0, false⟩, ⟨38, 55, 0, false⟩, ⟨40, 53, 0, false⟩, ⟨41, 52, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(10633823966279326983230456482242756608, 2), (10716900716015884225286944423510278144, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
