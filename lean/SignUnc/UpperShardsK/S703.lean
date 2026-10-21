import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_703 : segOK4 cfgK upperGroups (⟨(22756300211088023186871120384058231619584 : Int), 12, [⟨252, 281, 0, false⟩, ⟨256, 277, 0, false⟩, ⟨258, 275, 0, false⟩, ⟨260, 273, 0, false⟩, ⟨261, 272, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, false⟩, ⟨0, 1, 1, false⟩], [(42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
