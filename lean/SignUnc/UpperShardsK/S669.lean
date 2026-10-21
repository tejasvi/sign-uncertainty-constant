import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_669 : segOK4 cfgK upperGroups (⟨(15142482251232025066878113542772417888256 : Int), 12, [⟨164, 193, 0, false⟩, ⟨168, 189, 0, false⟩, ⟨170, 187, 0, false⟩, ⟨172, 185, 0, false⟩, ⟨173, 184, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 3), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
