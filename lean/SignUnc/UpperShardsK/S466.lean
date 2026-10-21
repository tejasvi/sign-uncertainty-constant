import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_466 : segOK4 cfgK upperGroups (⟨(1696011845871816096583201320976452157440 : Int), 16, [⟨7, 33, 0, false⟩, ⟨11, 29, 0, false⟩, ⟨13, 27, 0, true⟩, ⟨15, 25, 0, true⟩, ⟨16, 24, 0, true⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(5399988732876220733671716182388899840, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
