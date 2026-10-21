import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_138 : segOK4 cfgK upperGroups (⟨(598069521353475585564656689184887537664 : Int), 12, [⟨0, 21, 6, true⟩, ⟨0, 17, 2, true⟩, ⟨1, 15, 0, true⟩, ⟨3, 13, 0, true⟩, ⟨4, 12, 0, true⟩, ⟨48, 100, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
