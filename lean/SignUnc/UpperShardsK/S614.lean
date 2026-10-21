import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_614 : segOK4 cfgK upperGroups (⟨(6699226022006239442193131095871669141504 : Int), 6, [⟨64, 93, 0, false⟩, ⟨68, 89, 0, false⟩, ⟨70, 87, 0, false⟩, ⟨72, 85, 0, false⟩, ⟨73, 84, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 1), (31943010273706259570719613417362030592, 2)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
