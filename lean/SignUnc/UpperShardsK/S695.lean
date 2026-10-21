import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_695 : segOK4 cfgK upperGroups (⟨(20331788346776336634694576306106883112960 : Int), 6, [⟨224, 253, 0, false⟩, ⟨228, 249, 0, false⟩, ⟨230, 247, 0, false⟩, ⟨232, 245, 0, false⟩, ⟨233, 244, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, false⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 1), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
