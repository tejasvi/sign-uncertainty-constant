import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_427 : segOK4 cfgK upperGroups (⟨(1531519881393432757311355197266759516160 : Int), 16, [⟨6, 32, 0, false⟩, ⟨10, 28, 0, true⟩, ⟨12, 26, 0, true⟩, ⟨14, 24, 0, true⟩, ⟨15, 23, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(332306998946228968225951765070086144, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
