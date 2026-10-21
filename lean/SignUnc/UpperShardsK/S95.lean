import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_95 : segOK4 cfgK upperGroups (⟨(426599109897221437960065578408723087360 : Int), 14, [⟨0, 19, 8, true⟩, ⟨0, 15, 4, true⟩, ⟨0, 13, 2, true⟩, ⟨1, 11, 0, true⟩, ⟨2, 10, 0, true⟩, ⟨23, 75, 0, true⟩, ⟨56, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(1329227995784915872903807060280344576, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
