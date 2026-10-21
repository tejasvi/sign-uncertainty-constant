import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_598 : segOK4 cfgK upperGroups (⟨(4806405356008519239178109842032458465280 : Int), 6, [⟨44, 73, 0, false⟩, ⟨48, 69, 0, false⟩, ⟨50, 67, 0, false⟩, ⟨52, 65, 0, false⟩, ⟨53, 64, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 3), (42535295865117307932921825928971026432, 4), (15971505136853129785359806708681015296, 2)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
