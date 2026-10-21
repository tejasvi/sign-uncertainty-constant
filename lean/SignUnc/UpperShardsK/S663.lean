import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_663 : segOK4 cfgK upperGroups (⟨(14100367502536651022521528807512627740672 : Int), 6, [⟨152, 181, 0, false⟩, ⟨156, 177, 0, false⟩, ⟨158, 175, 0, false⟩, ⟨160, 173, 0, false⟩, ⟨161, 172, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 3), (42535295865117307932921825928971026432, 2), (21309186307426932587489156935119273984, 2)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
