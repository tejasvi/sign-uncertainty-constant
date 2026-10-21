import SUCert.Jet

/-!
# Contiguity and the base check for chains of checker-v4 segments (core Lean only)

`baseOK4` checks everything except the segment checks: the segments are contiguous from `⌊r 2^P⌋` with non-empty runs
of positive widths and counts and reach `Y`; `g(0) < 0`; the tail conditions at `Y`.  Soundness: `SignUnc.UpperK`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball

/-- The end of a contiguous chain of v4 segments from `lo` (every segment has non-empty runs with positive widths
and counts). -/
def contigEnd4 : Int → List Seg4 → Option Int
  | lo, [] => some lo
  | lo, s :: ss =>
    if s.lo = lo ∧ s.ws ≠ [] ∧ s.ws.all (fun r => decide (0 < r.1) && decide (0 < r.2)) = true then
      contigEnd4 (runsEnd s.lo s.ws) ss
    else none

/-- Everything except the segment checks (checker v4). -/
def baseOK4 (c : Cfg) (data : List GT) (segs : List Seg4) : Bool :=
  match prepAll c.P data with
  | some (T :: R) =>
    let lo0 : Int := ((c.rn * 2 ^ c.P / c.rd : Nat) : Int)
    decide (0 < c.rn ∧ 0 < c.rd ∧ 0 < c.Yd ∧ segs ≠ []) &&
    (match contigEnd4 lo0 segs with
      | some e => decide (((c.Yn * 2 ^ c.P : Nat) : Int) ≤ e * (c.Yd : Int))
      | none => false) &&
    (match sum01 c.P c.n c.k ⟨0, 0⟩ (T :: R) with
      | some (G0, _) => G0.isNeg
      | none => false) &&
    tailOK c.P c.n T R (ofRat c.P c.Yn c.Yd)
  | _ => false

end SignUnc.Chk
