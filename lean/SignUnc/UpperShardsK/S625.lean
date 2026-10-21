import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_625 : segOK4 cfgK upperGroups (⟨(8124158433487669257946012264492198526976 : Int), 6, [⟨80, 109, 0, false⟩, ⟨84, 105, 0, false⟩, ⟨86, 103, 0, false⟩, ⟨88, 101, 0, false⟩, ⟨89, 100, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 1), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
