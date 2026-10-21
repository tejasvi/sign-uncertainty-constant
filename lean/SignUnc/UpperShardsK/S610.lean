import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_610 : segOK4 cfgK upperGroups (⟨(6167534823692273093031608271759531311104 : Int), 6, [⟨60, 89, 0, false⟩, ⟨64, 85, 0, false⟩, ⟨66, 83, 0, false⟩, ⟨68, 81, 0, false⟩, ⟨69, 80, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 2), (21267647932558653966460912964485513216, 7)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
