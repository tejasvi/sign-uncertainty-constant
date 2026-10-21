import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_592 : segOK4 cfgK upperGroups (⟨(4338517101492228851915969756813777174528 : Int), 12, [⟨36, 65, 0, false⟩, ⟨40, 61, 0, false⟩, ⟨42, 59, 0, false⟩, ⟨44, 57, 0, false⟩, ⟨45, 56, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(10633823966279326983230456482242756608, 6)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
