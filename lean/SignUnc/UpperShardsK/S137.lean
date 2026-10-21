import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_137 : segOK4 cfgK upperGroups (⟨(596740293357690669691752882124607193088 : Int), 12, [⟨0, 21, 6, true⟩, ⟨0, 17, 2, true⟩, ⟨1, 15, 0, true⟩, ⟨3, 13, 0, true⟩, ⟨4, 12, 0, true⟩, ⟨48, 100, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(1329227995784915872903807060280344576, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
