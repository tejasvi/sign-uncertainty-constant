import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_653 : segOK4 cfgK upperGroups (⟨(12462758611729634667104038509247243223040 : Int), 6, [⟨132, 161, 0, false⟩, ⟨136, 157, 0, false⟩, ⟨138, 155, 0, false⟩, ⟨140, 153, 0, false⟩, ⟨141, 152, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 5), (21350724682295211208517400905753034752, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
