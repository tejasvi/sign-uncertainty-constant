import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_526 : segOK4 cfgK upperGroups (⟨(2461647171443927639375794187697930633216 : Int), 8, [⟨16, 45, 0, false⟩, ⟨20, 41, 0, false⟩, ⟨22, 39, 0, false⟩, ⟨24, 37, 0, true⟩, ⟨25, 36, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 5)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
