import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_616 : segOK4 cfgK upperGroups (⟨(7018240740994619251690044790338951839744 : Int), 6, [⟨68, 97, 0, false⟩, ⟨72, 93, 0, false⟩, ⟨74, 91, 0, false⟩, ⟨76, 89, 0, false⟩, ⟨77, 88, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 5), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
