import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_351 : segOK4 cfgK upperGroups (⟨(1270658887220643017253983061686741893120 : Int), 12, [⟨2, 28, 0, false⟩, ⟨6, 24, 0, true⟩, ⟨8, 22, 0, true⟩, ⟨10, 20, 0, true⟩, ⟨11, 19, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5399988732876220733671716182388899840, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
