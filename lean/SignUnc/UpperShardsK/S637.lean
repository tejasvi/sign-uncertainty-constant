import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_637 : segOK4 cfgK upperGroups (⟨(9676696732564450997497658910899640991744 : Int), 6, [⟨100, 129, 0, false⟩, ⟨104, 125, 0, false⟩, ⟨106, 123, 0, false⟩, ⟨108, 121, 0, false⟩, ⟨109, 120, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 5), (42535295865117307932921825928971026432, 1), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
