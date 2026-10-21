import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_582 : segOK4 cfgK upperGroups (⟨(3806825903178262502754446932701639344128 : Int), 12, [⟨32, 61, 0, false⟩, ⟨36, 57, 0, false⟩, ⟨38, 55, 0, false⟩, ⟨40, 53, 0, false⟩, ⟨41, 52, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(10633823966279326983230456482242756608, 1), (5316911983139663491615228241121378304, 2), (10633823966279326983230456482242756608, 3)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
