import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_628 : segOK4 cfgK upperGroups (⟨(8400637856610931759510004133030510198784 : Int), 6, [⟨84, 113, 0, false⟩, ⟨88, 109, 0, false⟩, ⟨90, 107, 0, false⟩, ⟨92, 105, 0, false⟩, ⟨93, 104, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 4), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
