import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_156 : segOK4 cfgK upperGroups (⟨(680813964091086598652918678687338987520 : Int), 14, [⟨0, 22, 5, true⟩, ⟨0, 18, 1, true⟩, ⟨2, 16, 0, true⟩, ⟨4, 14, 0, true⟩, ⟨5, 13, 0, true⟩, ⟨61, 113, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(332306998946228968225951765070086144, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
