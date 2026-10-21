import SUCert.Chk3

/-!
# Grid evaluation of the Gaussian combination (core Lean only)

The pairs of the certificate come in groups with a common width `a` and centres on an arithmetic grid
`s_k = s₀ + kΔ`.  On a group, `e^{-πa(y-s_k)²}` follows `E_{k+1} = E_k R_k`, `R_{k+1} = R_k ρ` (upward from the grid
point nearest to `y`, and the mirror recurrence downward), `e^{-πa(y+s_k)²}` follows the same recurrence from `k = 0`,
and `e^{2πi s_k y}` is a power recurrence of complex discs; only eight `exp`/`cos` evaluations per group remain.
-/

namespace SignUnc.Chk

open Ival Ival.Ball

/-- A group: width `a = an/ad`, centres `s₀ + kΔ` (`s₀ = s0n/s0d`, `Δ = dn/dd`), coefficients `cn/cd`. -/
structure GGroup where
  an : Nat
  ad : Nat
  s0n : Int
  s0d : Nat
  dn : Nat
  dd : Nat
  cs : List (Int × Nat)
deriving Repr, Inhabited

/-- The centre `s_k` as an exact fraction (numerator, denominator). -/
def GGroup.sk (g : GGroup) (k : Nat) : Int × Nat :=
  (g.s0n * (g.dd : Int) + (k : Int) * (g.dn : Int) * (g.s0d : Int), g.s0d * g.dd)

/-- Prepared balls of a group. -/
structure PG where
  A : Ball
  Ai : Ball
  Q : Ball
  S0 : Ball
  D : Ball
  rho : Ball
  pa : Ball
  g : GGroup
  CS : List (Ball × Ball)

/-- The balls `(c_k, s_k)` of the coefficients and centres. -/
def csBalls (P : Nat) (g : GGroup) : List (Ball × Ball) :=
  (List.range g.cs.length).zipWith (fun j c => (ofRat P c.1 c.2, ofRat P (g.sk j).1 (g.sk j).2)) g.cs

def prepGroup (P n : Nat) (g : GGroup) : Option PG :=
  if 0 < g.an ∧ 0 < g.ad ∧ 0 < g.s0d ∧ 0 < g.dn ∧ 0 < g.dd ∧ g.cs.all (fun c => decide (0 < c.2)) then
    (twoOverSqrt P g.an g.ad).bind fun Q =>
    (expB' P n (neg (mul P (mulInt 2 (mul P (piB P) (ofRat P g.an g.ad))) (mul P (ofRat P g.dn g.dd)
      (ofRat P g.dn g.dd))))).bind fun rho =>
      some ⟨ofRat P g.an g.ad, ofRat P g.ad g.an, Q, ofRat P g.s0n g.s0d, ofRat P g.dn g.dd, rho,
        mul P (piB P) (ofRat P g.an g.ad), g, csBalls P g⟩
  else none

/-- `[x, x r, x r (r ρ), …]` (`m` entries): the recurrence `E_{j+1} = E_j R_j`, `R_{j+1} = R_j ρ`. -/
def recList (P : Nat) (rho : Ball) : Nat → Ball → Ball → List Ball
  | 0, _, _ => []
  | m + 1, x, r => x :: recList P rho m (mul P x r) (mul P r rho)

/-- Complex powers `z, z w, z w², …` (`m` entries), as discs. -/
def powList (P : Nat) (w : CDisc) : Nat → CDisc → List CDisc
  | 0, _ => []
  | m + 1, z => z :: powList P w m (CDisc.mul P z w)

/-- The grid index nearest to the centre of `Y`, clamped to `[0, N-1]` (any value is sound). -/
def kStar (P : Nat) (g : GGroup) (Y : Ball) : Nat :=
  let num : Int := (Y.m * (g.s0d : Int) - g.s0n * ((2 ^ P : Nat) : Int)) * (g.dd : Int)
  let den : Int := ((2 ^ P * g.s0d * g.dn : Nat) : Int)
  let q := (2 * num + den) / (2 * den)
  if q < 0 then 0 else min q.toNat (g.cs.length - 1)

/-- The lists `E_k ∋ e^{-πa(y-s_k)²}`, `F_k ∋ e^{-πa(y+s_k)²}`, `Z_k ∋ e^{2πi s_k y}` and the ball of
`2a^{-1/2} e^{-πy²/a}`; `ex` is the exponential used (`expB'` at points, `expH` on intervals), `cz` the cos/sin. -/
def gridLists (P : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (G : PG) (Y : Ball) :
    Option (List Ball × List Ball × List CDisc × Ball) :=
  let N := G.g.cs.length
  let ks := kStar P G.g Y
  let u := sub Y (ofRat P (G.g.sk ks).1 (G.g.sk ks).2)
  let v0 := add Y G.S0
  let twoPaD := mul P (mulInt 2 G.pa) G.D
  let paD2 := mul P G.pa (mul P G.D G.D)
  (ex (neg (mul P G.pa (mul P u u)))).bind fun Ek =>
  (ex (sub (mul P twoPaD u) paD2)).bind fun Rup =>
  (ex (sub (neg (mul P twoPaD u)) paD2)).bind fun Rdn =>
  (ex (neg (mul P G.pa (mul P v0 v0)))).bind fun F0 =>
  (ex (sub (neg (mul P twoPaD v0)) paD2)).bind fun T0 =>
  (ex (neg (mul P (piB P) (mul P (mul P Y Y) G.Ai)))).bind fun H =>
  (cz (mul P G.S0 Y)).bind fun Z0 =>
  (cz (mul P G.D Y)).bind fun W =>
    some ((recList P G.rho ks (mul P Ek Rdn) (mul P Rdn G.rho)).reverse ++ recList P G.rho (N - ks) Ek Rup,
      recList P G.rho N F0 T0,
      powList P (CDisc.ofBalls W.1 W.2) N (CDisc.ofBalls Z0.1 Z0.2),
      mul P G.Q H)

/-- `c (gb + gbh, gb' + gbh', gb'' + gbh'')` for one centre, from `C ∋ c`, `s ∋ s_k`, `E`, `F`, `Z` and `QH`. -/
def row012 (P : Nat) (G : PG) (Y QH C s E Fm : Ball) (Z : CDisc) : Ball × Ball × Ball :=
  let PI := piB P
  let piy := mul P PI (mul P Y G.Ai)
  let pia := mul P PI G.Ai
  let pa2 := mul P G.pa G.pa
  let uj := sub Y s
  let vj := add Y s
  let pis := mul P PI s
  let val := add (add E Fm) (mul P QH Z.re)
  let d1 := add (neg (mul P (mulInt 2 G.pa) (add (mul P uj E) (mul P vj Fm))))
    (mul P QH (sub (neg (mul P (mulInt 2 piy) Z.re)) (mul P (mulInt 2 pis) Z.im)))
  let k1 := sub (sub (mulInt 4 (mul P piy piy)) (mulInt 2 pia)) (mulInt 4 (mul P pis pis))
  let k2 := mulInt 8 (mul P pis piy)
  let d2 := add (add (mul P (sub (mulInt 4 (mul P pa2 (mul P uj uj))) (mulInt 2 G.pa)) E)
      (mul P (sub (mulInt 4 (mul P pa2 (mul P vj vj))) (mulInt 2 G.pa)) Fm))
    (mul P QH (add (mul P k1 Z.re) (mul P k2 Z.im)))
  (mul P C val, mul P C d1, mul P C d2)

/-- `c (gb''' + gbh''')` for one centre. -/
def row3 (P : Nat) (G : PG) (Y QH C s E Fm : Ball) (Z : CDisc) : Ball :=
  let PI := piB P
  let piy := mul P PI (mul P Y G.Ai)
  let pia := mul P PI G.Ai
  let pa2 := mul P G.pa G.pa
  let pa3 := mul P pa2 G.pa
  let uj := sub Y s
  let vj := add Y s
  let pis := mul P PI s
  let e1 := sub (mulInt 12 (mul P pa2 uj)) (mulInt 8 (mul P pa3 (mul P uj (mul P uj uj))))
  let e2 := sub (mulInt 12 (mul P pa2 vj)) (mulInt 8 (mul P pa3 (mul P vj (mul P vj vj))))
  let k1 := sub (sub (mulInt 4 (mul P piy piy)) (mulInt 2 pia)) (mulInt 4 (mul P pis pis))
  let k2 := mulInt 8 (mul P pis piy)
  let l1 := add (add (neg (mul P (mulInt 2 piy) k1)) (mulInt 8 (mul P pia piy))) (mul P (mulInt 2 pis) k2)
  let l2 := add (sub (neg (mul P (mulInt 2 piy) k2)) (mul P (mulInt 2 pis) k1)) (mulInt 8 (mul P pis pia))
  mul P C (add (add (mul P e1 E) (mul P e2 Fm)) (mul P QH (add (mul P l1 Z.re) (mul P l2 Z.im))))

def add3 (a b : Ball × Ball × Ball) : Ball × Ball × Ball := (add a.1 b.1, add a.2.1 b.2.1, add a.2.2 b.2.2)

/-- Sum of `row012` over the rows. -/
def fold012 (P : Nat) (G : PG) (Y QH : Ball) :
    List (Ball × Ball) → List Ball → List Ball → List CDisc → Ball × Ball × Ball
  | (C, s) :: cs, E :: es, Fm :: fs, Z :: zs => add3 (row012 P G Y QH C s E Fm Z) (fold012 P G Y QH cs es fs zs)
  | _, _, _, _ => (⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩)

/-- Sum of `row3` over the rows. -/
def fold3 (P : Nat) (G : PG) (Y QH : Ball) : List (Ball × Ball) → List Ball → List Ball → List CDisc → Ball
  | (C, s) :: cs, E :: es, Fm :: fs, Z :: zs => add (row3 P G Y QH C s E Fm Z) (fold3 P G Y QH cs es fs zs)
  | _, _, _, _ => ⟨0, 0⟩

/-- Values and first two derivatives of a group at the point ball `Y`. -/
def group012 (P n k : Nat) (G : PG) (Y : Ball) : Option (Ball × Ball × Ball) :=
  (gridLists P (expB' P n) (cosSinTurn P n k) G Y).bind fun L =>
    some (fold012 P G Y L.2.2.2 G.CS L.1 L.2.1 L.2.2.1)

/-- Third derivative of a group on the ball `Y`. -/
def group3 (P n k : Nat) (G : PG) (Y : Ball) : Option Ball :=
  (gridLists P (expH P n) (cosSinTurnC P n k) G Y).bind fun L =>
    some (fold3 P G Y L.2.2.2 G.CS L.1 L.2.1 L.2.2.1)

def groups012 (P n k : Nat) (Y : Ball) : List PG → Option (Ball × Ball × Ball)
  | [] => some (⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩)
  | G :: L => (group012 P n k G Y).bind fun a => (groups012 P n k Y L).bind fun b => some (add3 a b)

def groups3 (P n k : Nat) (Y : Ball) : List PG → Option Ball
  | [] => some ⟨0, 0⟩
  | G :: L => (group3 P n k G Y).bind fun a => (groups3 P n k Y L).bind fun b => some (add a b)

def prepGroups (P n : Nat) : List GGroup → Option (List PG)
  | [] => some []
  | g :: L => (prepGroup P n g).bind fun G => (prepGroups P n L).bind fun Gs => some (G :: Gs)

/-- Third-order tests on `[lo, hi]` with the grid evaluation (same tests as `ivOK3`). -/
def ivOKg (P n k : Nat) (gs : List PG) (lo hi : Int) : Bool :=
  let y0 := (lo + hi) / 2
  let η : Nat := (max (y0 - lo) (hi - y0)).toNat
  let h : Nat := (hi - lo).toNat
  let p2 : Int := ((2 ^ P : Nat) : Int)
  match groups3 P n k ⟨y0, η⟩ gs with
  | none => false
  | some G3 =>
    let M3 : Int := (G3.absHi : Int)
    (match groups012 P n k ⟨y0, 0⟩ gs with
      | some (G0, G1, G2) =>
        let A := G0.m - (G0.r : Int)
        let B : Int := (G1.absHi : Int)
        let K := 3 * (G2.m - (G2.r : Int)) * p2 - M3 * (η : Int)
        (decide (0 < K) && decide (3 * B * B * p2 < 2 * K * A)) ||
        decide (0 < 6 * A * p2 * p2 * p2 - 6 * B * (η : Int) * p2 * p2 + min K 0 * (η : Int) * (η : Int))
      | none => false) ||
    (match groups012 P n k ⟨lo, 0⟩ gs with
      | some (G0, G1, G2) =>
        let A := G0.m - (G0.r : Int)
        let B := G1.m - (G1.r : Int)
        let K := 3 * (G2.m - (G2.r : Int)) * p2 - M3 * (h : Int)
        decide (0 < A) &&
        decide (0 < 6 * A * p2 * p2 * p2 + 6 * B * (h : Int) * p2 * p2 + min K 0 * (h : Int) * (h : Int))
      | none => false)

def rangeOKg (P n k : Nat) (gs : List PG) : Nat → Int → Int → Bool
  | 0, lo, hi => ivOKg P n k gs lo hi
  | d + 1, lo, hi => ivOKg P n k gs lo hi ||
      (rangeOKg P n k gs d lo ((lo + hi) / 2) && rangeOKg P n k gs d ((lo + hi) / 2) hi)

def piecesOKg (P n k : Nat) (gs : List PG) (d : Nat) (w : Int) : Nat → Int → Bool
  | 0, _ => true
  | c + 1, lo => rangeOKg P n k gs d lo (lo + w) && piecesOKg P n k gs d w c (lo + w)


/-! ## Matching the flat data, and the segment check -/

/-- The exact rational entries `(an, ad, s_k, c_k)` of a group. -/
def GGroup.raw (g : GGroup) : List (Nat × Nat × (Int × Nat) × (Int × Nat)) :=
  (List.range g.cs.length).zipWith (fun j c => (g.an, g.ad, g.sk j, c)) g.cs

/-- A flat entry equals a group entry as rationals (cross-multiplication). -/
def eqEntry (t : GT) (r : Nat × Nat × (Int × Nat) × (Int × Nat)) : Bool :=
  t.an * r.2.1 == r.1 * t.ad && t.sn * (r.2.2.1.2 : Int) == r.2.2.1.1 * (t.sd : Int) &&
    t.cn * (r.2.2.2.2 : Int) == r.2.2.2.1 * (t.cd : Int)

/-- The flat data are the entries of the last group followed by those of the other groups, in order. -/
def matchFlat (data : List GT) (gs : List GGroup) : Bool :=
  let raws := (gs.getLast?.map GGroup.raw).getD [] ++ (gs.dropLast.flatMap GGroup.raw)
  data.length == raws.length && (data.zip raws).all (fun p => eqEntry p.1 p.2)

/-- One segment of the range check with the grid evaluation. -/
def segOKg (c : Cfg) (gs : List GGroup) (s : Seg) : Bool :=
  match prepGroups c.P c.n gs with
  | some pgs => piecesOKg c.P c.n c.k pgs c.depth s.w s.m s.lo
  | none => false


/-- The pairs of a group as flat entries. -/
def GGroup.gts (g : GGroup) : List GT :=
  (List.range g.cs.length).zipWith (fun j c => ⟨g.an, g.ad, (g.sk j).1, (g.sk j).2, c.1, c.2⟩) g.cs

/-- Flat data from the groups: the pairs of the last group (the wide pair), then those of the other groups. -/
def flatOfGroups (gs : List GGroup) : List GT :=
  (gs.getLast?.map GGroup.gts).getD [] ++ gs.dropLast.flatMap GGroup.gts

end SignUnc.Chk
