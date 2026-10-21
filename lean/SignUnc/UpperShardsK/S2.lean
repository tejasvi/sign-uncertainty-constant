import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_2 : segOK4 cfgK upperGroups (⟨(187710786185954671248142535057963672299 : Int), 14, [⟨0, 16, 11, true⟩, ⟨0, 12, 7, true⟩, ⟨0, 10, 5, true⟩, ⟨0, 8, 3, true⟩, ⟨0, 7, 1, true⟩, ⟨0, 38, 0, true⟩, ⟨0, 45, 0, true⟩, ⟨0, 1, 1, false⟩], [(332306998946228968225951765070086144, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
