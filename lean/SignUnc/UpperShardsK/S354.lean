import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_354 : segOK4 cfgK upperGroups (⟨(1276308106202728909713824241692933357568 : Int), 16, [⟨3, 29, 0, false⟩, ⟨7, 25, 0, true⟩, ⟨9, 23, 0, true⟩, ⟨11, 21, 0, true⟩, ⟨12, 20, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(332306998946228968225951765070086144, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
