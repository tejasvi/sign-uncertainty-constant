import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_490 : segOK4 cfgK upperGroups (⟨(2041694201525630780780247644590609268736 : Int), 6, [⟨12, 41, 0, false⟩, ⟨16, 37, 0, false⟩, ⟨18, 35, 0, true⟩, ⟨20, 33, 0, true⟩, ⟨21, 32, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(83076749736557242056487941267521536, 1), (166153499473114484112975882535043072, 1), (332306998946228968225951765070086144, 1), (664613997892457936451903530140172288, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
