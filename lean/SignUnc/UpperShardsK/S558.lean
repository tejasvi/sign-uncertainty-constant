import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_558 : segOK4 cfgK upperGroups (⟨(3065116681530279445674122593065207070720 : Int), 8, [⟨24, 53, 0, false⟩, ⟨28, 49, 0, false⟩, ⟨30, 47, 0, false⟩, ⟨32, 45, 0, true⟩, ⟨33, 44, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 1), (5316911983139663491615228241121378304, 4)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
