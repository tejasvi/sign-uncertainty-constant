import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_651 : segOK4 cfgK upperGroups (⟨(12058673301011020241741281162922018471936 : Int), 6, [⟨128, 157, 0, false⟩, ⟨132, 153, 0, false⟩, ⟨134, 151, 0, false⟩, ⟨136, 149, 0, false⟩, ⟨137, 148, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 8), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
