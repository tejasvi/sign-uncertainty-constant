import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_639 : segOK4 cfgK upperGroups (⟨(10038246747417948114927494431295894716416 : Int), 6, [⟨104, 133, 0, false⟩, ⟨108, 129, 0, false⟩, ⟨110, 127, 0, false⟩, ⟨112, 125, 0, false⟩, ⟨113, 124, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 7), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
