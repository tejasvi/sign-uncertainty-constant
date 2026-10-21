import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_66 : segOK4 cfgK upperGroups (⟨(340282366920938463463374607431768211456 : Int), 14, [⟨0, 18, 9, true⟩, ⟨0, 14, 5, true⟩, ⟨0, 12, 3, true⟩, ⟨0, 10, 1, true⟩, ⟨1, 9, 0, true⟩, ⟨11, 63, 0, true⟩, ⟨31, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(83076749736557242056487941267521536, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
