import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_681 : segOK4 cfgK upperGroups (⟨(17162908804825097193691900274398541643776 : Int), 6, [⟨188, 217, 0, false⟩, ⟨192, 213, 0, false⟩, ⟨194, 211, 0, false⟩, ⟨196, 209, 0, false⟩, ⟨197, 208, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 3), (42535295865117307932921825928971026432, 2), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
