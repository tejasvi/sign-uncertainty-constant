import SUCert.LowCfg
import SUCert.LowSegs
import SignUnc.LowK.MomsLit16
import SignUnc.LowK.MomsLit20

/-!
# Kernel shards of the lower check: definitions (core Lean only)

The moments `ps.map (pieceMoms P M N)` of the 19 pieces of `P` are the dominant shared cost of a segment check in the
kernel. `lsegM` is `lsegOK` with these moments passed as an argument; the shards evaluate `lsegM` with the literal
tables `MomsLit20` (`M = 20`, `N = 25`) and `MomsLit16` (`M = 16`, `N = 135`, truncated to `N`), and two kernel
equations identify the tables with the computed moments. `ppOK` is one piece of `pOK`.
-/

deriving instance DecidableEq for Ival.Ball

namespace SignUnc.Chk

open Ival

/-- `lsegOK` with the moments of the pieces of `P` passed as an argument. -/
def lsegM (c : LCfg) (gs : List GGroup) (cos : List (Nat × Nat × Int × Nat)) (ps : List PPiece) (s : LSeg)
    (moms : List (List (List Ball))) : Bool :=
  match prepGroupsV c.P c.n gs with
  | some pgs =>
    match omitAll c.P c.n s.lo (runsEnd s.lo s.ws) pgs s.sps with
    | some R =>
      lrunsOK c.P c.n c.k s.M s.N c.dm pgs s.sps cos ps moms (pmaxHi ps) R
        (c.m + (Ball.mul c.P (Ball.mulInt 2 (Ball.ofRat c.P 2751 5000)) ⟨(c.eps : Int), 0⟩).absHi) s.lo s.ws
    | none => false
  | none => false

/-- One piece of `pOK` (with `prepGroupsV` inside). -/
def ppOK (P n k D L : Nat) (gs : List GGroup) (cos : List (Nat × Nat × Int × Nat)) (psi : List (Int × Nat))
    (eps : Nat) (x : PPiece × List GSpec) : Bool :=
  match prepGroupsV P n gs with
  | some pgs => pieceP_OK' P n k D L pgs cos (psiPoly P psi) eps x
  | none => false

end SignUnc.Chk

namespace SignUnc.LowData

open SignUnc.Chk Ival

/-- The moment table used by the shards of a segment with Taylor order `M` and series length `N`. -/
def momsFor (M N : Nat) : List (List (List Ball)) :=
  if M = 20 then MomsLit20 else MomsLit16.map (fun a => a.map (·.take N))

end SignUnc.LowData
