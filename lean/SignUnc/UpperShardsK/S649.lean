import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_649 : segOK4 cfgK upperGroups (⟨(11803461525820316394143750207348192313344 : Int), 6, [⟨124, 153, 0, false⟩, ⟨128, 149, 0, false⟩, ⟨130, 147, 0, false⟩, ⟨132, 145, 0, false⟩, ⟨133, 144, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 4), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
