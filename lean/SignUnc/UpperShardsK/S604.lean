import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_604 : segOK4 cfgK upperGroups (⟨(5486970089850396166104859056895994888192 : Int), 6, [⟨52, 81, 0, false⟩, ⟨56, 77, 0, false⟩, ⟨58, 75, 0, false⟩, ⟨60, 73, 0, false⟩, ⟨61, 72, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 4), (21267647932558653966460912964485513216, 5)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
