import SignUnc.LowK.Defs

namespace SignUnc.LowData
open SignUnc.Chk

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem kmisc : chainOK 0 lowP = true ∧ lowP.length = lowPSS.length ∧ lowPS.length = 19 ∧
    (match lcontigEnd ((2751 * 2 ^ lowCfg.P / 5000 : Nat) : Int) lowSegs with
      | some e => decide (((lowCfg.YT * 2 ^ lowCfg.P : Nat) : Int) ≤ e)
      | none => false) = true := by
  decide +kernel

end SignUnc.LowData
