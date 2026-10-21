import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_671 : segOK4 cfgK upperGroups (⟨(15525299914018080838274409976133157126144 : Int), 6, [⟨168, 197, 0, false⟩, ⟨172, 193, 0, false⟩, ⟨174, 191, 0, false⟩, ⟨176, 189, 0, false⟩, ⟨177, 188, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 5), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
