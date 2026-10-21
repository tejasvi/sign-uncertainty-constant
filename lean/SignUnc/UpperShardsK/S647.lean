import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_647 : segOK4 cfgK upperGroups (⟨(11378108567169143314814531948058482049024 : Int), 6, [⟨120, 149, 0, false⟩, ⟨124, 145, 0, false⟩, ⟨126, 143, 0, false⟩, ⟨128, 141, 0, false⟩, ⟨129, 140, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 8), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
