import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_540 : segOK4 cfgK upperGroups (⟨(2722258935367507707706996859454145691648 : Int), 8, [⟨20, 49, 0, false⟩, ⟨24, 45, 0, false⟩, ⟨26, 43, 0, false⟩, ⟨28, 41, 0, true⟩, ⟨29, 40, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(83076749736557242056487941267521536, 1), (166153499473114484112975882535043072, 1), (332306998946228968225951765070086144, 1), (664613997892457936451903530140172288, 1), (1329227995784915872903807060280344576, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
