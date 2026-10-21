import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_633 : segOK4 cfgK upperGroups (⟨(9081202590452808686436753347894046621696 : Int), 6, [⟨92, 121, 0, false⟩, ⟨96, 117, 0, false⟩, ⟨98, 115, 0, false⟩, ⟨100, 113, 0, false⟩, ⟨101, 112, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 4), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
