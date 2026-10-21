import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_643 : segOK4 cfgK upperGroups (⟨(10697543833327266387887782733194945626112 : Int), 6, [⟨112, 141, 0, false⟩, ⟨116, 137, 0, false⟩, ⟨118, 135, 0, false⟩, ⟨120, 133, 0, false⟩, ⟨121, 132, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 8), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
