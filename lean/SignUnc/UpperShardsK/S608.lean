import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_608 : segOK4 cfgK upperGroups (⟨(5954858344366686553366999142114676178944 : Int), 12, [⟨56, 85, 0, false⟩, ⟨60, 81, 0, false⟩, ⟨62, 79, 0, false⟩, ⟨64, 77, 0, false⟩, ⟨65, 76, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(42535295865117307932921825928971026432, 3), (42618372614853865174978313870238547968, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
