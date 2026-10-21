import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_536 : segOK4 cfgK upperGroups (⟨(2671665194777944347294595703222225076224 : Int), 8, [⟨16, 45, 0, false⟩, ⟨20, 41, 0, false⟩, ⟨22, 39, 0, false⟩, ⟨24, 37, 0, true⟩, ⟨25, 36, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 5)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
