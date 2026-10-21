import SUCert.LowP

/-! The parameters of the lower check (`m = 1e-4`, `ε = 5e-7`, `δ = 1e-6`, each rounded up to units `2^-128`) and the
included Gaussian terms per piece of `P`. -/

namespace SignUnc.LowData
open SignUnc.Chk

def lowEps : Nat := (5 * 2 ^ 128 + 10000000 - 1) / 10000000
def lowDelta : Nat := (1 * 2 ^ 128 + 1000000 - 1) / 1000000
def lowM : Nat := (1 * 2 ^ 128 + 10000 - 1) / 10000

def lowCfg : LCfg := ⟨128, 24, 4, 24, 8, 8, lowM, lowEps, lowDelta, 30, 300⟩

def lowPSS : List (List GSpec) := lowPS.map (·.2)

end SignUnc.LowData
