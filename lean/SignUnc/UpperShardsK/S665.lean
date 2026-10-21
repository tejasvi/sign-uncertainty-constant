import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_665 : segOK4 cfgK upperGroups (⟨(14440649869457589485984903414944395952128 : Int), 6, [⟨156, 185, 0, false⟩, ⟨160, 181, 0, false⟩, ⟨162, 179, 0, false⟩, ⟨164, 177, 0, false⟩, ⟨165, 176, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 8), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
