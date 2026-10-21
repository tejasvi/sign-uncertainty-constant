import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_677 : segOK4 cfgK upperGroups (⟨(16482344070983220266765151059535005220864 : Int), 6, [⟨180, 209, 0, false⟩, ⟨184, 205, 0, false⟩, ⟨186, 203, 0, false⟩, ⟨188, 201, 0, false⟩, ⟨189, 200, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 7), (42535295865117307932921825928971026432, 1), (83076749736557242056487941267521536, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
