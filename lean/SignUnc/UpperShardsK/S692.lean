import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_692 : segOK4 cfgK upperGroups (⟨(19693758908799577015700748917172317716480 : Int), 6, [⟨216, 245, 0, false⟩, ⟨220, 241, 0, false⟩, ⟨222, 239, 0, false⟩, ⟨224, 237, 0, false⟩, ⟨225, 236, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, false⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 1), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
