import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_686 : segOK4 cfgK upperGroups (⟨(18332629441115823161847250487445244870656 : Int), 12, [⟨200, 229, 0, false⟩, ⟨204, 225, 0, false⟩, ⟨206, 223, 0, false⟩, ⟨208, 221, 0, false⟩, ⟨209, 220, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, false⟩, ⟨0, 1, 1, false⟩], [(42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
