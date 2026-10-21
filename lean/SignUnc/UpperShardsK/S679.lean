import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_679 : segOK4 cfgK upperGroups (⟨(16822626437904158730228525666966773432320 : Int), 6, [⟨184, 213, 0, false⟩, ⟨188, 209, 0, false⟩, ⟨190, 207, 0, false⟩, ⟨192, 205, 0, false⟩, ⟨193, 204, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 8), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
