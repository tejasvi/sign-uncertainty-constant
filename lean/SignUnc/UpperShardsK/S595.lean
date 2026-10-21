import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_595 : segOK4 cfgK upperGroups (⟨(4466122989087580775714735234600690253824 : Int), 6, [⟨40, 69, 0, false⟩, ⟨44, 65, 0, false⟩, ⟨46, 63, 0, false⟩, ⟨48, 61, 0, false⟩, ⟨49, 60, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 9)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
