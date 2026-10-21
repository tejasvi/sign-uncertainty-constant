import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_599 : segOK4 cfgK upperGroups (⟨(5072292493540370692379899498059161141248 : Int), 6, [⟨44, 73, 0, false⟩, ⟨48, 69, 0, false⟩, ⟨50, 67, 0, false⟩, ⟨52, 65, 0, false⟩, ⟨53, 64, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(15971505136853129785359806708681015296, 2)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
