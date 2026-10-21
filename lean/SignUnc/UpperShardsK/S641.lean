import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_641 : segOK4 cfgK upperGroups (⟨(10357261466406327924424408125763177414656 : Int), 6, [⟨108, 137, 0, false⟩, ⟨112, 133, 0, false⟩, ⟨114, 131, 0, false⟩, ⟨116, 129, 0, false⟩, ⟨117, 128, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 3), (42535295865117307932921825928971026432, 2), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
