import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_613 : segOK4 cfgK upperGroups (⟨(6507817190613211556494982879191299522560 : Int), 6, [⟨64, 93, 0, false⟩, ⟨68, 89, 0, false⟩, ⟨70, 87, 0, false⟩, ⟨72, 85, 0, false⟩, ⟨73, 84, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 9)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
