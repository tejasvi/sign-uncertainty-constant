import SUCert.UpperCfgK
import SUCert.DataGroups

namespace SignUnc.UpperRunK
open SignUnc.Chk SignUnc.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem shardK_601 : segOK4 cfgK upperGroups (⟨(5167955370862016356607945362428712189952 : Int), 8, [⟨48, 77, 0, false⟩, ⟨52, 73, 0, false⟩, ⟨54, 71, 0, false⟩, ⟨56, 69, 0, false⟩, ⟨57, 68, 0, false⟩, ⟨131, 131, 0, true⟩, ⟨71, 71, 0, true⟩, ⟨0, 1, 1, false⟩], [(21267647932558653966460912964485513216, 10)]⟩ : Seg4) = true := by decide +kernel

end SignUnc.UpperRunK
