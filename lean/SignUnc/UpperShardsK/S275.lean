import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_275 : segOK4 cfgK upperGroups (⟨(991521008105810683944183579027869532160 : Int), 16, [⟨0, 25, 2, true⟩, ⟨3, 21, 0, true⟩, ⟨5, 19, 0, true⟩, ⟨7, 17, 0, true⟩, ⟨8, 16, 0, true⟩, ⟨98, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
