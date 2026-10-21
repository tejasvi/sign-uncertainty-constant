import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_635 : segOK4 cfgK upperGroups (⟨(9378949661508629841967206129396843806720 : Int), 6, [⟨96, 125, 0, false⟩, ⟨100, 121, 0, false⟩, ⟨102, 119, 0, false⟩, ⟨104, 117, 0, false⟩, ⟨105, 116, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 6), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
