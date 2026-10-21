import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_645 : segOK4 cfgK upperGroups (⟨(11037826200248204851351157340626713837568 : Int), 6, [⟨116, 145, 0, false⟩, ⟨120, 141, 0, false⟩, ⟨122, 139, 0, false⟩, ⟨124, 137, 0, false⟩, ⟨125, 136, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 1), (42535295865117307932921825928971026432, 3), (21309186307426932587489156935119273984, 2)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
