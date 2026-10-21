import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_178 : segOK4 cfgK upperGroups (⟨(765635325572111542792592866721478475776 : Int), 12, [⟨0, 23, 4, true⟩, ⟨1, 19, 0, true⟩, ⟨3, 17, 0, true⟩, ⟨5, 15, 0, true⟩, ⟨6, 14, 0, true⟩, ⟨73, 125, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(83076749736557242056487941267521536, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
