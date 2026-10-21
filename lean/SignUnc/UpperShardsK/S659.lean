import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_659 : segOK4 cfgK upperGroups (⟨(13355999824897098133695396853755634778112 : Int), 12, [⟨144, 173, 0, false⟩, ⟨148, 169, 0, false⟩, ⟨150, 167, 0, false⟩, ⟨152, 165, 0, false⟩, ⟨153, 164, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 5), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
