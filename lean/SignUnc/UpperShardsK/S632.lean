import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_632 : segOK4 cfgK upperGroups (⟨(8889793759059780800738605131213677002752 : Int), 6, [⟨92, 121, 0, false⟩, ⟨96, 117, 0, false⟩, ⟨98, 115, 0, false⟩, ⟨100, 113, 0, false⟩, ⟨101, 112, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 9)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
