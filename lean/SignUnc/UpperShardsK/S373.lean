import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_373 : segOK4 cfgK upperGroups (⟨(1355729478950877633119826713544683945984 : Int), 16, [⟨3, 29, 0, false⟩, ⟨7, 25, 0, true⟩, ⟨9, 23, 0, true⟩, ⟨11, 21, 0, true⟩, ⟨12, 20, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5399988732876220733671716182388899840, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
