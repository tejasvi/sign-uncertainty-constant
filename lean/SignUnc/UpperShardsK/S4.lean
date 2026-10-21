import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_4 : segOK4 cfgK upperGroups (⟨(188707707182793358152820390353173930731 : Int), 14, [⟨0, 16, 11, true⟩, ⟨0, 12, 7, true⟩, ⟨0, 10, 5, true⟩, ⟨0, 8, 3, true⟩, ⟨0, 7, 1, true⟩, ⟨0, 38, 0, true⟩, ⟨0, 45, 0, true⟩, ⟨0, 1, 1, false⟩], [(1329227995784915872903807060280344576, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
