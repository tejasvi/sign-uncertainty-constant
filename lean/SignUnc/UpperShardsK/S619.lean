import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_619 : segOK4 cfgK upperGroups (⟨(7454269061986939936623521750081538621440 : Int), 6, [⟨72, 101, 0, false⟩, ⟨76, 97, 0, false⟩, ⟨78, 95, 0, false⟩, ⟨80, 93, 0, false⟩, ⟨81, 92, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(31943010273706259570719613417362030592, 1)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
