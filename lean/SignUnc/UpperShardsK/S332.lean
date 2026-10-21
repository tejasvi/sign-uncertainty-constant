import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_332 : segOK4 cfgK upperGroups (⟨(1191071360973021179363867613952456261632 : Int), 12, [⟨2, 28, 0, false⟩, ⟨6, 24, 0, true⟩, ⟨8, 22, 0, true⟩, ⟨10, 20, 0, true⟩, ⟨11, 19, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(166153499473114484112975882535043072, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
