import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_252 : segOK4 cfgK upperGroups (⟨(936025739281790446250449634261165146112 : Int), 16, [⟨0, 25, 2, true⟩, ⟨3, 21, 0, true⟩, ⟨5, 19, 0, true⟩, ⟨7, 17, 0, true⟩, ⟨8, 16, 0, true⟩, ⟨98, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(332306998946228968225951765070086144, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
