import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_621 : segOK4 cfgK upperGroups (⟨(7528664291376026946885106701486604156928 : Int), 6, [⟨76, 105, 0, false⟩, ⟨80, 101, 0, false⟩, ⟨82, 99, 0, false⟩, ⟨84, 97, 0, false⟩, ⟨85, 96, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 9)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
