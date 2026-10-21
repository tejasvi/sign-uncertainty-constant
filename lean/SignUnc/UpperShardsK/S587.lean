import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_587 : segOK4 cfgK upperGroups (⟨(4083388403051261561560495289181218537472 : Int), 12, [⟨36, 65, 0, false⟩, ⟨40, 61, 0, false⟩, ⟨42, 59, 0, false⟩, ⟨44, 57, 0, false⟩, ⟨45, 56, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(83076749736557242056487941267521536, 1), (166153499473114484112975882535043072, 1), (332306998946228968225951765070086144, 1), (664613997892457936451903530140172288, 1), (1329227995784915872903807060280344576, 1), (2658455991569831745807614120560689152, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
