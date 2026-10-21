import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_618 : segOK4 cfgK upperGroups (⟨(7188381924455088483421732094054835945472 : Int), 6, [⟨72, 101, 0, false⟩, ⟨76, 97, 0, false⟩, ⟨78, 95, 0, false⟩, ⟨80, 93, 0, false⟩, ⟨81, 92, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 5), (42535295865117307932921825928971026432, 3), (31943010273706259570719613417362030592, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
