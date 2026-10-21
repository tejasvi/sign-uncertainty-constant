import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_374 : segOK4 cfgK upperGroups (⟨(1361129467683753853853498429727072845824 : Int), 14, [⟨4, 30, 0, false⟩, ⟨8, 26, 0, true⟩, ⟨10, 24, 0, true⟩, ⟨12, 22, 0, true⟩, ⟨13, 21, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(83076749736557242056487941267521536, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
