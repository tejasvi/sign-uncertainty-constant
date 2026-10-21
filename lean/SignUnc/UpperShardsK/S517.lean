import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_517 : segOK4 cfgK upperGroups (⟨(2302139811949737734627337340464289284096 : Int), 6, [⟨12, 41, 0, false⟩, ⟨16, 37, 0, false⟩, ⟨18, 35, 0, true⟩, ⟨20, 33, 0, true⟩, ⟨21, 32, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 4)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
