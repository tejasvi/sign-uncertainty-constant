import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_285 : segOK4 cfgK upperGroups (⟨(1022093252008863749020971141414317457408 : Int), 12, [⟨0, 26, 1, true⟩, ⟨4, 22, 0, true⟩, ⟨6, 20, 0, true⟩, ⟨8, 18, 0, true⟩, ⟨9, 17, 0, true⟩, ⟨111, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(1329227995784915872903807060280344576, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
