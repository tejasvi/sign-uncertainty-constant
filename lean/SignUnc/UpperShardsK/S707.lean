import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_707 : segOK4 cfgK upperGroups (⟨(23787822674191986182865502906806412771328 : Int), 8, [⟨264, 293, 0, false⟩, ⟨268, 289, 0, false⟩, ⟨270, 287, 0, false⟩, ⟨272, 285, 0, false⟩, ⟨273, 284, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, false⟩, ⟨0, 1, 1, false⟩], [(31943010273706259570719613417362030592, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
