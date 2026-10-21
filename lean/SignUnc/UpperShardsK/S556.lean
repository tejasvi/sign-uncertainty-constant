import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_556 : segOK4 cfgK upperGroups (⟨(3057141313555569950436699750703525003264 : Int), 8, [⟨20, 49, 0, false⟩, ⟨24, 45, 0, false⟩, ⟨26, 43, 0, false⟩, ⟨28, 41, 0, true⟩, ⟨29, 40, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5399988732876220733671716182388899840, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
