import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_667 : segOK4 cfgK upperGroups (⟨(14802199884311086603414738935340649676800 : Int), 6, [⟨160, 189, 0, false⟩, ⟨164, 185, 0, false⟩, ⟨166, 183, 0, false⟩, ⟨168, 181, 0, false⟩, ⟨169, 180, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 1), (21267647932558653966460912964485513216, 5), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
