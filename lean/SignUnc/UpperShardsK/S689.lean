import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_689 : segOK4 cfgK upperGroups (⟨(19013194174957700088773999702308781293568 : Int), 6, [⟨208, 237, 0, false⟩, ⟨212, 233, 0, false⟩, ⟨214, 231, 0, false⟩, ⟨216, 229, 0, false⟩, ⟨217, 228, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, false⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 1), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
