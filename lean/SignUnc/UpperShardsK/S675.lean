import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_675 : segOK4 cfgK upperGroups (⟨(16290935239590192381067002842854635601920 : Int), 6, [⟨176, 205, 0, false⟩, ⟨180, 201, 0, false⟩, ⟨182, 199, 0, false⟩, ⟨184, 197, 0, false⟩, ⟨185, 196, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 1), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
