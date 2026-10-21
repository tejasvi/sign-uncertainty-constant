import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_673 : segOK4 cfgK upperGroups (⟨(15801779337141343339838401844671468797952 : Int), 6, [⟨172, 201, 0, false⟩, ⟨176, 197, 0, false⟩, ⟨178, 195, 0, false⟩, ⟨180, 193, 0, false⟩, ⟨181, 192, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 8), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
