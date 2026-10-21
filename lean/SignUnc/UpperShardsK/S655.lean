import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_655 : segOK4 cfgK upperGroups (⟨(12739238034852897168668030377785554894848 : Int), 6, [⟨136, 165, 0, false⟩, ⟨140, 161, 0, false⟩, ⟨142, 159, 0, false⟩, ⟨144, 157, 0, false⟩, ⟨145, 156, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 8), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
