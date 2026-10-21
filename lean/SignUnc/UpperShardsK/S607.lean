import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_607 : segOK4 cfgK upperGroups (⟨(5790034072889356985126927066639913451520 : Int), 12, [⟨56, 85, 0, false⟩, ⟨60, 81, 0, false⟩, ⟨62, 79, 0, false⟩, ⟨64, 77, 0, false⟩, ⟨65, 76, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 1), (10633823966279326983230456482242756608, 1), (21267647932558653966460912964485513216, 1), (42535295865117307932921825928971026432, 3)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
