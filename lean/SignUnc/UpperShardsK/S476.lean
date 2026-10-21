import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_476 : segOK4 cfgK upperGroups (⟨(1866153029332285328314888624692336263168 : Int), 8, [⟨8, 37, 0, false⟩, ⟨12, 33, 0, false⟩, ⟨14, 31, 0, true⟩, ⟨16, 29, 0, true⟩, ⟨17, 28, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5316911983139663491615228241121378304, 4)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
