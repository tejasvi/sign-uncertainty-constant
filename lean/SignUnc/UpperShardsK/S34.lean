import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_34 : segOK4 cfgK upperGroups (⟨(256457926436752206228378274692838981632 : Int), 16, [⟨0, 17, 10, true⟩, ⟨0, 13, 6, true⟩, ⟨0, 11, 4, true⟩, ⟨0, 9, 2, true⟩, ⟨0, 8, 1, true⟩, ⟨0, 50, 0, true⟩, ⟨6, 70, 0, true⟩, ⟨0, 1, 1, false⟩], [(1329227995784915872903807060280344576, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
