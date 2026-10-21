import SUCert.Chk

/-!
# Third-order tests for the upper-bound check (core Lean only)

Point evaluations of `g, g', g''` and an interval bound of `g'''`; the tests are justified by `taylor3_lower`
(centred) and `taylor3_right` (left-anchored) in `SignUnc.Calc3`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball

/-- `(c (gb + gbh), c (gb' + gbh'), c (gb'' + gbh''))` at the ball `Y` (a point). -/
def term012 (P n k : Nat) (t : PT) (Y : Ball) : Option (Ball × Ball × Ball) :=
  (expB' P n (neg (mul P (mul P (piB P) t.A) (mul P (sub Y t.S) (sub Y t.S))))).bind fun E1 =>
  (expB' P n (neg (mul P (mul P (piB P) t.A) (mul P (add Y t.S) (add Y t.S))))).bind fun E2 =>
  (expB' P n (neg (mul P (piB P) (mul P (mul P Y Y) t.Ai)))).bind fun H =>
  (cosSinTurn P n k (mul P t.S Y)).bind fun cs =>
    let PI := piB P
    let d1 := sub Y t.S
    let d2 := add Y t.S
    let pa := mul P PI t.A
    let QH := mul P t.Q H
    let v0 := add (add E1 E2) (mul P QH cs.1)
    let gb1 := neg (mul P (mulInt 2 pa) (add (mul P d1 E1) (mul P d2 E2)))
    let piy := mul P PI (mul P Y t.Ai)
    let pis := mul P PI t.S
    let gbh1 := mul P QH (sub (neg (mul P (mulInt 2 piy) cs.1)) (mul P (mulInt 2 pis) cs.2))
    let pa2 := mul P pa pa
    let c1 := sub (mulInt 4 (mul P pa2 (mul P d1 d1))) (mulInt 2 pa)
    let c2 := sub (mulInt 4 (mul P pa2 (mul P d2 d2))) (mulInt 2 pa)
    let gb2 := add (mul P c1 E1) (mul P c2 E2)
    let k1 := sub (sub (mulInt 4 (mul P piy piy)) (mulInt 2 (mul P PI t.Ai))) (mulInt 4 (mul P pis pis))
    let k2 := mulInt 8 (mul P pis piy)
    let gbh2 := mul P QH (add (mul P k1 cs.1) (mul P k2 cs.2))
    some (mul P t.C v0, mul P t.C (add gb1 gbh1), mul P t.C (add gb2 gbh2))

/-- `c (gb''' + gbh''')` on the ball `Y` (end-point hulls for exp, centred form for cos/sin). -/
def term3 (P n k : Nat) (t : PT) (Y : Ball) : Option Ball :=
  (expH P n (neg (mul P (mul P (piB P) t.A) (mul P (sub Y t.S) (sub Y t.S))))).bind fun E1 =>
  (expH P n (neg (mul P (mul P (piB P) t.A) (mul P (add Y t.S) (add Y t.S))))).bind fun E2 =>
  (expH P n (neg (mul P (piB P) (mul P (mul P Y Y) t.Ai)))).bind fun H =>
  (cosSinTurnC P n k (mul P t.S Y)).bind fun cs =>
    let PI := piB P
    let d1 := sub Y t.S
    let d2 := add Y t.S
    let pa := mul P PI t.A
    let QH := mul P t.Q H
    let pa2 := mul P pa pa
    let pa3 := mul P pa2 pa
    let e1 := sub (mulInt 12 (mul P pa2 d1)) (mulInt 8 (mul P pa3 (mul P d1 (mul P d1 d1))))
    let e2 := sub (mulInt 12 (mul P pa2 d2)) (mulInt 8 (mul P pa3 (mul P d2 (mul P d2 d2))))
    let gb3 := add (mul P e1 E1) (mul P e2 E2)
    let piy := mul P PI (mul P Y t.Ai)
    let pis := mul P PI t.S
    let pia := mul P PI t.Ai
    let k1 := sub (sub (mulInt 4 (mul P piy piy)) (mulInt 2 pia)) (mulInt 4 (mul P pis pis))
    let k2 := mulInt 8 (mul P pis piy)
    let l1 := add (add (neg (mul P (mulInt 2 piy) k1)) (mulInt 8 (mul P pia piy))) (mul P (mulInt 2 pis) k2)
    let l2 := add (sub (neg (mul P (mulInt 2 piy) k2)) (mul P (mulInt 2 pis) k1)) (mulInt 8 (mul P pis pia))
    let gbh3 := mul P QH (add (mul P l1 cs.1) (mul P l2 cs.2))
    some (mul P t.C (add gb3 gbh3))

def sum012 (P n k : Nat) (Y : Ball) : List PT → Option (Ball × Ball × Ball)
  | [] => some (⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩)
  | t :: L => (term012 P n k t Y).bind fun a => (sum012 P n k Y L).bind fun b =>
      some (add a.1 b.1, add a.2.1 b.2.1, add a.2.2 b.2.2)

def sum3 (P n k : Nat) (Y : Ball) : List PT → Option Ball
  | [] => some ⟨0, 0⟩
  | t :: L => (term3 P n k t Y).bind fun a => (sum3 P n k Y L).bind fun c => some (add a c)

/-- Third-order tests on `[lo, hi]` (`M₃` bounds the third derivative on the piece; `K = 3 g₂ 2^P - M₃ η` with
`g₂` the lower end of the second derivative at the centre): convex case `K > 0` and `3 B² 2^P < 2 K A`, or the
general centred bound, or the left-anchored bound with the signed first derivative at `lo`. -/
def ivOK3 (P n k : Nat) (pts : List PT) (lo hi : Int) : Bool :=
  let y0 := (lo + hi) / 2
  let η : Nat := (max (y0 - lo) (hi - y0)).toNat
  let h : Nat := (hi - lo).toNat
  let p2 : Int := ((2 ^ P : Nat) : Int)
  match sum3 P n k ⟨y0, η⟩ pts with
  | none => false
  | some G3 =>
    let M3 : Int := (G3.absHi : Int)
    (match sum012 P n k ⟨y0, 0⟩ pts with
      | some (G0, G1, G2) =>
        let A := G0.m - (G0.r : Int)
        let B : Int := (G1.absHi : Int)
        let K := 3 * (G2.m - (G2.r : Int)) * p2 - M3 * (η : Int)
        (decide (0 < K) && decide (3 * B * B * p2 < 2 * K * A)) ||
        decide (0 < 6 * A * p2 * p2 * p2 - 6 * B * (η : Int) * p2 * p2 + min K 0 * (η : Int) * (η : Int))
      | none => false) ||
    (match sum012 P n k ⟨lo, 0⟩ pts with
      | some (G0, G1, G2) =>
        let A := G0.m - (G0.r : Int)
        let B := G1.m - (G1.r : Int)
        let K := 3 * (G2.m - (G2.r : Int)) * p2 - M3 * (h : Int)
        decide (0 < A) &&
        decide (0 < 6 * A * p2 * p2 * p2 + 6 * B * (h : Int) * p2 * p2 + min K 0 * (h : Int) * (h : Int))
      | none => false)

def rangeOK3 (P n k : Nat) (pts : List PT) : Nat → Int → Int → Bool
  | 0, lo, hi => ivOK3 P n k pts lo hi
  | d + 1, lo, hi => ivOK3 P n k pts lo hi ||
      (rangeOK3 P n k pts d lo ((lo + hi) / 2) && rangeOK3 P n k pts d ((lo + hi) / 2) hi)

def piecesOK3 (P n k : Nat) (pts : List PT) (d : Nat) (w : Int) : Nat → Int → Bool
  | 0, _ => true
  | c + 1, lo => rangeOK3 P n k pts d lo (lo + w) && piecesOK3 P n k pts d w c (lo + w)

/-- One segment of the range check with the third-order tests. -/
def segOK3 (c : Cfg) (data : List GT) (s : Seg) : Bool :=
  match prepAll c.P data with
  | some pts => piecesOK3 c.P c.n c.k pts c.depth s.w s.m s.lo
  | none => false

end SignUnc.Chk
