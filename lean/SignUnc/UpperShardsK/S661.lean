import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_661 : segOK4 cfgK upperGroups (⟨(13717549839750595251125232374151888502784 : Int), 8, [⟨148, 177, 0, false⟩, ⟨152, 173, 0, false⟩, ⟨154, 171, 0, false⟩, ⟨156, 169, 0, false⟩, ⟨157, 168, 0, false⟩, ⟨131, 131, 0, false⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 6), (42535295865117307932921825928971026432, 1), (31943010273706259570719613417362030592, 2)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
