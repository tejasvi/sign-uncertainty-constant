import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_253 : segOK4 cfgK upperGroups (⟨(936358046280736675218675586026235232256 : Int), 16, [⟨0, 25, 2, true⟩, ⟨3, 21, 0, true⟩, ⟨5, 19, 0, true⟩, ⟨7, 17, 0, true⟩, ⟨8, 16, 0, true⟩, ⟨98, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(664613997892457936451903530140172288, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
