import SUCert.IvalCore

/-!
# Checker for the upper-bound certificate (core Lean only)

Data: a list of Gaussian pairs `(a, s, c) = (an/ad, sn/sd, cn/cd)`, the wide pair `T` first.  The checker verifies

* `g(0) < 0` (ball evaluation);
* `g > 0` on `[r, Y]`: pieces of width `w` (units `2^-P`) from `⌊r 2^P⌋`, each bisected up to `depth` times, accepted
  when `g(y₀) - |g'(y₀)| η - M η²/2 > 0` with `M` an upper bound of `|g''|` on the piece (ball evaluation on the
  whole piece);
* the tail conditions of `SignUnc.tail_pos` at `Y` (all strict inequalities between balls).

Soundness: `SignUnc.ChkSound`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball

/-- A Gaussian pair `(a, s, c) = (an/ad, sn/sd, cn/cd)`. -/
structure GT where
  an : Nat
  ad : Nat
  sn : Int
  sd : Nat
  cn : Int
  cd : Nat
deriving Repr, Inhabited

/-- Balls for `a, s, c, 1/a, 2/√a`. -/
structure PT where
  A : Ball
  S : Ball
  C : Ball
  Ai : Ball
  Q : Ball
deriving Repr, Inhabited

/-- Newton iteration for `⌊√N⌋` (the caller checks the result). -/
def isqrtAux (N : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (x + N / x) / 2
    if y < x then isqrtAux N fuel y else x

/-- `⌊√N⌋` (unchecked). -/
def isqrt (N : Nat) : Nat := if N = 0 then 0 else isqrtAux N 400 (2 ^ (Nat.log2 N / 2 + 1))

/-- A ball containing `2/√a`, `a = an/ad`: `m² ≤ ⌊4 ad 2^{2P} / an⌋ < (m+1)²`. -/
def twoOverSqrt (P an ad : Nat) : Option Ball :=
  let N := 4 * ad * 2 ^ (2 * P) / an
  let m := isqrt N
  if 0 < an ∧ m * m ≤ N ∧ N < (m + 1) * (m + 1) then some ⟨m, 1⟩ else none

/-- Balls of one pair. -/
def prep (P : Nat) (t : GT) : Option PT :=
  if 0 < t.an ∧ 0 < t.ad ∧ 0 < t.sd ∧ 0 < t.cd then
    match twoOverSqrt P t.an t.ad with
    | some Q => some ⟨ofRat P t.an t.ad, ofRat P t.sn t.sd, ofRat P t.cn t.cd, ofRat P t.ad t.an, Q⟩
    | none => none
  else none

def prepAll (P : Nat) : List GT → Option (List PT)
  | [] => some []
  | t :: L =>
    match prep P t, prepAll P L with
    | some p, some ps => some (p :: ps)
    | _, _ => none

/-- `(c (gb + gbh), c (gb' + gbh'))` on the ball `Y`. -/
def term01 (P n k : Nat) (t : PT) (Y : Ball) : Option (Ball × Ball) :=
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
    some (mul P t.C v0, mul P t.C (add gb1 gbh1))

/-- `c (gb'' + gbh'')` on the ball `Y` (exp by end-point hulls, cos/sin by the centred form). -/
def term2 (P n k : Nat) (t : PT) (Y : Ball) : Option Ball :=
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
    let c1 := sub (mulInt 4 (mul P pa2 (mul P d1 d1))) (mulInt 2 pa)
    let c2 := sub (mulInt 4 (mul P pa2 (mul P d2 d2))) (mulInt 2 pa)
    let gb2 := add (mul P c1 E1) (mul P c2 E2)
    let piy := mul P PI (mul P Y t.Ai)
    let pis := mul P PI t.S
    let k1 := sub (sub (mulInt 4 (mul P piy piy)) (mulInt 2 (mul P PI t.Ai))) (mulInt 4 (mul P pis pis))
    let k2 := mulInt 8 (mul P pis piy)
    let gbh2 := mul P QH (add (mul P k1 cs.1) (mul P k2 cs.2))
    some (mul P t.C (add gb2 gbh2))

def sum01 (P n k : Nat) (Y : Ball) : List PT → Option (Ball × Ball)
  | [] => some (⟨0, 0⟩, ⟨0, 0⟩)
  | t :: L => (term01 P n k t Y).bind fun ab => (sum01 P n k Y L).bind fun cd =>
      some (add ab.1 cd.1, add ab.2 cd.2)

def sum2 (P n k : Nat) (Y : Ball) : List PT → Option Ball
  | [] => some ⟨0, 0⟩
  | t :: L => (term2 P n k t Y).bind fun a => (sum2 P n k Y L).bind fun c => some (add a c)

/-- The second-order tests on the piece `[lo, hi]` (units `2^-P`): centred at the midpoint with `|g'|`, or
anchored at `lo` with the signed `g'(lo)` (concave quadratic lower bound, checked at both ends). -/
def ivOK (P n k : Nat) (pts : List PT) (lo hi : Int) : Bool :=
  let y0 := (lo + hi) / 2
  let η : Nat := (max (y0 - lo) (hi - y0)).toNat
  match sum2 P n k ⟨y0, η⟩ pts with
  | none => false
  | some G2 =>
    (match sum01 P n k ⟨y0, 0⟩ pts with
      | some (G0, G1) =>
        decide (0 < 2 * (G0.m - (G0.r : Int)) * ((2 ^ (2 * P) : Nat) : Int)
          - ((2 * G1.absHi * η * 2 ^ P : Nat) : Int) - ((G2.absHi * η * η : Nat) : Int))
      | none => false) ||
    (match sum01 P n k ⟨lo, 0⟩ pts with
      | some (G0, G1) =>
        decide (0 < G0.m - (G0.r : Int)) &&
        decide (0 < 2 * (G0.m - (G0.r : Int)) * ((2 ^ (2 * P) : Nat) : Int)
          + 2 * (G1.m - (G1.r : Int)) * (((hi - lo).toNat : Nat) : Int) * ((2 ^ P : Nat) : Int)
          - ((G2.absHi * (hi - lo).toNat * (hi - lo).toNat : Nat) : Int))
      | none => false)

def rangeOK (P n k : Nat) (pts : List PT) : Nat → Int → Int → Bool
  | 0, lo, hi => ivOK P n k pts lo hi
  | d + 1, lo, hi => ivOK P n k pts lo hi ||
      (rangeOK P n k pts d lo ((lo + hi) / 2) && rangeOK P n k pts d ((lo + hi) / 2) hi)

def piecesOK (P n k : Nat) (pts : List PT) (d : Nat) (w : Int) : Nat → Int → Bool
  | 0, _ => true
  | c + 1, lo => rangeOK P n k pts d lo (lo + w) && piecesOK P n k pts d w c (lo + w)

/-- `π a_T (Y - s_T)²`. -/
def tailBase (P : Nat) (T : PT) (YB : Ball) : Ball :=
  mul P (mul P (piB P) T.A) (mul P (sub YB T.S) (sub YB T.S))

/-- Ball of `Rpair`. -/
def rpairB (P n : Nat) (T : PT) (YB : Ball) (t : PT) : Option Ball :=
  (expB' P n (add (neg (mul P (mul P (piB P) t.A) (mul P (sub YB t.S) (sub YB t.S)))) (tailBase P T YB))).bind
    fun e1 =>
  (expB' P n (add (neg (mul P (mul P (piB P) t.A) (mul P (add YB t.S) (add YB t.S)))) (tailBase P T YB))).bind
    fun e2 =>
  (expB' P n (add (neg (mul P (mul P (piB P) t.Ai) (mul P YB YB))) (tailBase P T YB))).bind fun e3 =>
    some (add (add e1 e2) (mul P t.Q e3))

/-- The conditions `PairCond` of one pair, as strict ball inequalities. -/
def pairCondB (P : Nat) (T : PT) (YB : Ball) (t : PT) : Bool :=
  (sub t.A T.A).isPos &&
  (sub (mul P (sub t.A T.A) YB) (sub (mul P t.A t.S) (mul P T.A T.S))).isPos &&
  (sub (mul P (sub t.A T.A) YB) (sub (neg (mul P t.A t.S)) (mul P T.A T.S))).isPos &&
  (sub t.Ai T.A).isPos &&
  (sub (mul P (sub t.Ai T.A) YB) (neg (mul P T.A T.S))).isPos

/-- `Σ |c| Rpair` with all pair conditions. -/
def tailSumB (P n : Nat) (T : PT) (YB : Ball) : List PT → Option Ball
  | [] => some ⟨0, 0⟩
  | t :: L =>
    if pairCondB P T YB t then
      (rpairB P n T YB t).bind fun R => (tailSumB P n T YB L).bind fun S => some (add (mul P (absB t.C) R) S)
    else none

/-- The tail test at `Y`. -/
def tailOK (P n : Nat) (T : PT) (R : List PT) (YB : Ball) : Bool :=
  T.C.isPos && (sub T.Ai T.A).isPos && (sub (mul P (sub T.Ai T.A) YB) (neg (mul P T.A T.S))).isPos &&
  (match expB' P n (add (neg (mul P (mul P (piB P) T.Ai) (mul P YB YB))) (tailBase P T YB)),
      tailSumB P n T YB R with
    | some e3, some S => (sub (sub T.C (mul P T.C (mul P T.Q e3))) S).isPos
    | _, _ => false)

/-- Parameters of a run. -/
structure Cfg where
  P : Nat
  n : Nat
  k : Nat
  rn : Nat
  rd : Nat
  Yn : Nat
  Yd : Nat
  w : Nat
  cnt : Nat
  depth : Nat
deriving Repr

/-- The whole check. -/
def checkUpper (c : Cfg) (data : List GT) : Bool :=
  match prepAll c.P data with
  | some (T :: R) =>
    let lo0 : Int := ((c.rn * 2 ^ c.P / c.rd : Nat) : Int)
    decide (0 < c.rn ∧ 0 < c.rd ∧ 0 < c.Yd ∧ 0 < c.w ∧ 0 < c.cnt) &&
    decide (c.Yn * 2 ^ c.P ≤ (c.rn * 2 ^ c.P / c.rd + c.cnt * c.w) * c.Yd) &&
    (match sum01 c.P c.n c.k ⟨0, 0⟩ (T :: R) with
      | some (G0, _) => G0.isNeg
      | none => false) &&
    tailOK c.P c.n T R (ofRat c.P c.Yn c.Yd) &&
    piecesOK c.P c.n c.k (T :: R) c.depth (c.w : Int) c.cnt lo0
  | _ => false

/-- A segment of `m` pieces of width `w` from `lo` (units `2^-P`). -/
structure Seg where
  lo : Int
  w : Nat
  m : Nat
deriving Repr

/-- One segment of the range check (one `native_decide` each). -/
def segOK (c : Cfg) (data : List GT) (s : Seg) : Bool :=
  match prepAll c.P data with
  | some pts => piecesOK c.P c.n c.k pts c.depth s.w s.m s.lo
  | none => false

/-- The end of a contiguous chain of segments starting at `lo` (all `m, w > 0`). -/
def contigEnd : Int → List Seg → Option Int
  | lo, [] => some lo
  | lo, s :: ss => if s.lo = lo ∧ 0 < s.m ∧ 0 < s.w then contigEnd (s.lo + (s.m : Int) * (s.w : Int)) ss else none

/-- Everything except the segment checks. -/
def baseOK (c : Cfg) (data : List GT) (segs : List Seg) : Bool :=
  match prepAll c.P data with
  | some (T :: R) =>
    let lo0 : Int := ((c.rn * 2 ^ c.P / c.rd : Nat) : Int)
    decide (0 < c.rn ∧ 0 < c.rd ∧ 0 < c.Yd ∧ segs ≠ []) &&
    (match contigEnd lo0 segs with
      | some e => decide (((c.Yn * 2 ^ c.P : Nat) : Int) ≤ e * (c.Yd : Int))
      | none => false) &&
    (match sum01 c.P c.n c.k ⟨0, 0⟩ (T :: R) with
      | some (G0, _) => G0.isNeg
      | none => false) &&
    tailOK c.P c.n T R (ofRat c.P c.Yn c.Yd)
  | _ => false

end SignUnc.Chk
