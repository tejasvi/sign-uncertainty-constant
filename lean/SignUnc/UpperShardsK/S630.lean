import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_630 : segOK4 cfgK upperGroups (⟨(8634581983869076953141074175639850844160 : Int), 12, [⟨88, 117, 0, false⟩, ⟨92, 113, 0, false⟩, ⟨94, 111, 0, false⟩, ⟨96, 109, 0, false⟩, ⟨97, 108, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 4), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
