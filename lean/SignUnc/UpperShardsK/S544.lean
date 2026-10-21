import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_544 : segOK4 cfgK upperGroups (⟨(2767369610474458290143669811562409885696 : Int), 8, [⟨20, 49, 0, false⟩, ⟨24, 45, 0, false⟩, ⟨26, 43, 0, false⟩, ⟨28, 41, 0, true⟩, ⟨29, 40, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(2658455991569831745807614120560689152, 5)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
