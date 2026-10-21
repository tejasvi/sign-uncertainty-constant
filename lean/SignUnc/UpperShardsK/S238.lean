import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_238 : segOK4 cfgK upperGroups (⟨(903791960384006236332532313049366790144 : Int), 12, [⟨0, 24, 3, true⟩, ⟨2, 20, 0, true⟩, ⟨4, 18, 0, true⟩, ⟨6, 16, 0, true⟩, ⟨7, 15, 0, true⟩, ⟨86, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
