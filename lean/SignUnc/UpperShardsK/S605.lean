import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_605 : segOK4 cfgK upperGroups (⟨(5763449512973658667668850925434306560000 : Int), 6, [⟨52, 81, 0, false⟩, ⟨56, 77, 0, false⟩, ⟨58, 75, 0, false⟩, ⟨60, 73, 0, false⟩, ⟨61, 72, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
