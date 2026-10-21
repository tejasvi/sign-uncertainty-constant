import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_315 : segOK4 cfgK upperGroups (⟨(1108493071734883280759718600332539854848 : Int), 12, [⟨1, 27, 0, true⟩, ⟨5, 23, 0, true⟩, ⟨7, 21, 0, true⟩, ⟨9, 19, 0, true⟩, ⟨10, 18, 0, true⟩, ⟨123, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
