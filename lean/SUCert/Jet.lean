import SUCert.Grid

/-!
# Order-`m` Taylor models of the Gaussian combination (checker v4, core Lean only)

For a group with width `a` and a range of included terms, the normalized Taylor coefficients
`T_j(y₀) = g^{(j)}(y₀)/j!` of the included terms are computed from moments:

* `e^{-πa(y₀+t-s)²} = E · e^{α t} e^{-πa t²}` with `α = -2πa(y₀-s)`, so the E-terms contribute
  `Σ_p g_{j-p} μ_p / p!` with `μ_p = Σ c E α^p` and `g` the coefficients of `e^{-πa t²}`; the mirror terms
  (`y₀ + s`) likewise;
* `Q e^{-π(y₀+t)²/a} cos(2πs(y₀+t))` is the real part of `Q H Z e^{(α_R + iω) t - (π/a) t²}` with
  `α_R = -2πy₀/a`, `ω = 2πs`, so these terms contribute `Q H Σ_p h_{j-p} ν_p / p!` with
  `ν_p = Re Σ c Z (iω)^p` and `h` the coefficients of `e^{α_R t - (π/a) t²}`.

A piece `[y₀ - η, y₀ + η]` is accepted when the Taylor polynomial of order `m` at `y₀`, minus the bound of
`|T_{m+1}|` on the piece times `η^{m+1}` and the bound of the omitted terms, is positive on the piece; the
positivity of the integer polynomial is decided by bisection with exact Taylor shifts.
Soundness: `SignUnc.JetSound`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball

/-! ## Series and moments -/

/-- `[e_j, e_{j+1}, …]` (`fuel` entries) from `e_j = e0`, `e_{j+1} = e1` and
`e_{i+2} = (α e_{i+1} + 2β e_i)/(i+2)` (`be2 = 2β`). -/
def eserAux (P : Nat) (al be2 : Ball) : Nat → Nat → Ball → Ball → List Ball
  | 0, _, _, _ => []
  | fuel + 1, j, e0, e1 =>
    e0 :: eserAux P al be2 fuel (j + 1) e1 (divNat (j + 2) (add (mul P al e1) (mul P be2 e0)))

/-- `[e_0, …, e_n]`: the Taylor coefficients of `exp(α t + β t²)`. -/
def eser (P n : Nat) (al be : Ball) : List Ball := eserAux P al (mulInt 2 be) (n + 1) 0 (ofInt P 1) al

/-- `[w, w a, …, w a^(n-1)]`. -/
def powsW (P : Nat) (a : Ball) : Nat → Ball → List Ball
  | 0, _ => []
  | n + 1, w => w :: powsW P a n (mul P w a)

/-- `[x, y, x b, y b, x b², y b², …]` (`n` entries). -/
def pows2 (P : Nat) (b : Ball) : Nat → Ball → Ball → List Ball
  | 0, _, _ => []
  | n + 1, x, y => x :: pows2 P b n y (mul P x b)

def zeroL (n : Nat) : List Ball := List.replicate n ⟨0, 0⟩

def addL (a b : List Ball) : List Ball := List.zipWith add a b

/-- Moments `Σ_k w_k a_k^p` (`p ≤ n`) of the pairs `(w_k, a_k)`. -/
def momW (P n : Nat) : List (Ball × Ball) → List Ball
  | (w, a) :: L => addL (powsW P a (n + 1) w) (momW P n L)
  | [] => zeroL (n + 1)

/-- Moments `Σ_k (x_k, y_k, x_k b_k, y_k b_k, …)_p` (`p ≤ n`) of the triples `(x_k, y_k, b_k)`. -/
def momW2 (P n : Nat) : List (Ball × Ball × Ball) → List Ball
  | (x, y, b) :: L => addL (pows2 P b (n + 1) x y) (momW2 P n L)
  | [] => zeroL (n + 1)

/-- Moments `Σ c E α^p` of the rows `(c, s)` and values `E`, with `α = -tpa (Y - s)`. -/
def momE (P n : Nat) (tpa Y : Ball) (rows : List (Ball × Ball)) (Es : List Ball) : List Ball :=
  momW P n (List.zipWith (fun r E => (mul P r.1 E, neg (mul P tpa (sub Y r.2)))) rows Es)

/-- Moments `Σ c F α^p` with `α = -tpa (Y + s)` (mirror terms). -/
def momF (P n : Nat) (tpa Y : Ball) (rows : List (Ball × Ball)) (Fs : List Ball) : List Ball :=
  momW P n (List.zipWith (fun r F => (mul P r.1 F, neg (mul P tpa (add Y r.2)))) rows Fs)

/-- Moments `Re Σ c Z (iω)^p` from the rows `(c, ω, -ω²)` and the discs `Z`. -/
def momH (P n : Nat) (rows : List (Ball × Ball × Ball)) (Zs : List CDisc) : List Ball :=
  momW2 P n (List.zipWith (fun r Z => (mul P r.1 Z.re, neg (mul P r.2.1 (mul P r.1 Z.im)), r.2.2)) rows Zs)

/-- Entry `p` divided by `p!` (`f = p!` along the list). -/
def divFactAux : Nat → Nat → List Ball → List Ball
  | _, _, [] => []
  | p, f, b :: bs => divNat f b :: divFactAux (p + 1) (f * (p + 1)) bs

def divFact (L : List Ball) : List Ball := divFactAux 0 1 L

/-- `Σ a_i b_i`. -/
def dot (P : Nat) : List Ball → List Ball → Ball
  | a :: as, b :: bs => add (mul P a b) (dot P as bs)
  | _, _ => ⟨0, 0⟩

/-- Entry `j`: `Σ_{p ≤ j} μ_p g_{j-p}` (`rg` holds `g_{j-1}, …, g_0`). -/
def convAux (P : Nat) (μ : List Ball) : List Ball → List Ball → List Ball
  | [], _ => []
  | g :: gs, rg => dot P μ (g :: rg) :: convAux P μ gs (g :: rg)

/-- The truncated product of the series `g` and `μ` (as many entries as `g`). -/
def conv (P : Nat) (g μ : List Ball) : List Ball := convAux P μ g []

/-! ## Groups -/

/-- A prepared group with the rows `(c, ω, -ω²)`, `ω = 2πs`. -/
structure PG4 where
  G : PG
  OM : List (Ball × Ball × Ball)

def prepGroup4 (P n : Nat) (g : GGroup) : Option PG4 :=
  (prepGroup P n g).bind fun G =>
    some ⟨G, G.CS.map fun cs => (cs.1, mul P (mulInt 2 (piB P)) cs.2,
      neg (mul P (mul P (mulInt 2 (piB P)) cs.2) (mul P (mulInt 2 (piB P)) cs.2)))⟩

def prepGroups4 (P n : Nat) : List GGroup → Option (List PG4)
  | [] => some []
  | g :: L => (prepGroup4 P n g).bind fun G => (prepGroups4 P n L).bind fun Gs => some (G :: Gs)

/-- Included terms of a group: E-terms `k ∈ [k1, k2)`, mirror terms `k ∈ [0, kF)`, the cosine terms iff `hz`. -/
structure GSpec where
  k1 : Nat
  k2 : Nat
  kF : Nat
  hz : Bool
deriving Repr

/-- `E_k ∋ e^{-πa(y-s_k)²}` for `k ∈ [k1, k2)` (recurrences from the grid point nearest to `Y`). -/
def gridE (P : Nat) (ex : Ball → Option Ball) (G : PG) (Y : Ball) (k1 k2 : Nat) : Option (List Ball) :=
  if k1 < k2 then
    let ks := min (max (kStar P G.g Y) k1) (k2 - 1)
    let u := sub Y (ofRat P (G.g.sk ks).1 (G.g.sk ks).2)
    let twoPaD := mul P (mulInt 2 G.pa) G.D
    let paD2 := mul P G.pa (mul P G.D G.D)
    (ex (neg (mul P G.pa (mul P u u)))).bind fun Ek =>
    (ex (sub (mul P twoPaD u) paD2)).bind fun Rup =>
    (ex (sub (neg (mul P twoPaD u)) paD2)).bind fun Rdn =>
      some ((recList P G.rho (ks - k1) (mul P Ek Rdn) (mul P Rdn G.rho)).reverse ++ recList P G.rho (k2 - ks) Ek Rup)
  else some []

/-- `F_k ∋ e^{-πa(y+s_k)²}` for `k ∈ [0, kF)`. -/
def gridF (P : Nat) (ex : Ball → Option Ball) (G : PG) (Y : Ball) (kF : Nat) : Option (List Ball) :=
  if 0 < kF then
    let v0 := add Y G.S0
    let twoPaD := mul P (mulInt 2 G.pa) G.D
    let paD2 := mul P G.pa (mul P G.D G.D)
    (ex (neg (mul P G.pa (mul P v0 v0)))).bind fun F0 =>
    (ex (sub (neg (mul P twoPaD v0)) paD2)).bind fun T0 =>
      some (recList P G.rho kF F0 T0)
  else some []

/-- `Q H ∋ 2a^{-1/2} e^{-πy²/a}` and `Z_k ∋ e^{2πi s_k y}` for all `k`. -/
def gridH (P : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (G : PG) (Y : Ball) :
    Option (Ball × List CDisc) :=
  (ex (neg (mul P (piB P) (mul P (mul P Y Y) G.Ai)))).bind fun H =>
  (cz (mul P G.S0 Y)).bind fun Z0 =>
  (cz (mul P G.D Y)).bind fun W =>
    some (mul P G.Q H, powList P (CDisc.ofBalls W.1 W.2) G.g.cs.length (CDisc.ofBalls Z0.1 Z0.2))

/-- `[T_0, …, T_n]` of the included terms of a group at `Y`. -/
def groupJet (P n : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (G : PG4) (sp : GSpec)
    (Y : Ball) : Option (List Ball) :=
  (gridE P ex G.G Y sp.k1 sp.k2).bind fun Es =>
  (gridF P ex G.G Y sp.kF).bind fun Fs =>
    let tpa := mulInt 2 G.G.pa
    let tE := conv P (eser P n ⟨0, 0⟩ (neg G.G.pa))
      (divFact (addL (momE P n tpa Y (G.G.CS.drop sp.k1) Es) (momF P n tpa Y G.G.CS Fs)))
    if sp.hz then
      (gridH P ex cz G.G Y).bind fun HZ =>
        let gH := eser P n (neg (mul P (mulInt 2 (piB P)) (mul P Y G.G.Ai))) (neg (mul P (piB P) G.G.Ai))
        some (addL tE ((conv P gH (divFact (momH P n G.OM HZ.2))).map (mul P HZ.1)))
    else some tE

/-- Sum of the group jets. -/
def jetAll (P n : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (Y : Ball) :
    List PG4 → List GSpec → Option (List Ball)
  | [], [] => some (zeroL (n + 1))
  | G :: Gs, sp :: sps =>
    (groupJet P n ex cz G sp Y).bind fun a => (jetAll P n ex cz Y Gs sps).bind fun b => some (addL a b)
  | _, _ => none

/-! ## Omitted terms -/

/-- `2 e^{-πa D²}` (upper end, units `2^-P`), after checking `D > 0` and `2πaDΔ > 1`: then
`Σ_{i ≥ 0} e^{-πa(D + iΔ)²} ≤ 2 e^{-πa D²}`. -/
def gaussTail (P n : Nat) (G : PG) (D : Ball) : Option Nat :=
  if D.isPos && (sub (mul P (mul P (mulInt 2 G.pa) D) G.D) (ofInt P 1)).isPos then
    (expB' P n (neg (mul P G.pa (mul P D D)))).map fun e => 2 * e.absHi
  else none

/-- Upper bound (units `2^-P`) of `max_k |c_k|`. -/
def cmaxHi (G : PG) : Nat := G.CS.foldr (fun cs acc => max cs.1.absHi acc) 0

/-- Upper bound (units `2^-P`) of `Σ_k |c_k|`. -/
def csumHi (G : PG) : Nat := G.CS.foldr (fun cs acc => cs.1.absHi + acc) 0

/-- Bound (units `2^-P`) of the omitted terms of a group for `y ∈ [ylo, yhi]` (`0 ≤ ylo`). -/
def omitG (P n : Nat) (G : PG) (sp : GSpec) (ylo yhi : Int) : Option Nat :=
  let N := G.g.cs.length
  let cm := cmaxHi G
  let tl : Option Nat := if 0 < sp.k1 then
      gaussTail P n G (sub ⟨ylo, 0⟩ (ofRat P (G.g.sk (sp.k1 - 1)).1 (G.g.sk (sp.k1 - 1)).2)) else some 0
  let th : Option Nat := if sp.k2 < N then
      gaussTail P n G (sub (ofRat P (G.g.sk sp.k2).1 (G.g.sk sp.k2).2) ⟨yhi, 0⟩) else some 0
  let tf : Option Nat := if sp.kF < N then
      gaussTail P n G (add ⟨ylo, 0⟩ (ofRat P (G.g.sk sp.kF).1 (G.g.sk sp.kF).2)) else some 0
  let thz : Option Nat := if sp.hz then some 0 else
      (expB' P n (neg (mul P (piB P) (mul P (mul P ⟨ylo, 0⟩ ⟨ylo, 0⟩) G.Ai)))).map fun e =>
        cdiv ((mul P G.Q e).absHi * csumHi G) (2 ^ P)
  if 0 ≤ ylo ∧ sp.k1 ≤ sp.k2 ∧ sp.k2 ≤ N ∧ sp.kF ≤ N then
    tl.bind fun a => th.bind fun b => tf.bind fun c => thz.bind fun d =>
      some (cdiv (cm * (a + b + c)) (2 ^ P) + d)
  else none

def omitAll (P n : Nat) (ylo yhi : Int) : List PG4 → List GSpec → Option Nat
  | [], [] => some 0
  | G :: Gs, sp :: sps => (omitG P n G.G sp ylo yhi).bind fun a => (omitAll P n ylo yhi Gs sps).bind fun b => some (a + b)
  | _, _ => none

/-! ## Positivity of an integer polynomial on `[-1, 1]` -/

/-- Coefficients of `p(x + s)` from those of `p(x)` (lowest degree first). -/
def tshift (s : Int) : List Int → List Int
  | [] => []
  | c :: cs => List.zipWith (· + ·) (c :: tshift s cs) ((tshift s cs).map (s * ·) ++ [0])

/-- `[b_0 2^e, b_1 2^(e-d), b_2 2^(e-2d), …]`. -/
def scaleAux (d : Nat) : Nat → List Int → List Int
  | _, [] => []
  | e, b :: bs => b * ((2 ^ e : Nat) : Int) :: scaleAux d (e - d) bs

/-- `D_0 - Σ_{l ≥ 1} |D_l|`: a lower bound of the polynomial `D` on `[-1, 1]`. -/
def lowB : List Int → Int
  | [] => 0
  | c :: cs => c - ((cs.map Int.natAbs).sum : Nat)

/-- The test of one node: `K 2^{dm} < lowB` of the polynomial `2^{dm} Σ_j b_j ((n0 + ρ)/2^d)^j` in `ρ`. -/
def nodeOK (m : Nat) (b : List Int) (K d : Nat) (n0 : Int) : Bool :=
  decide (((K * 2 ^ (d * m) : Nat) : Int) < lowB (tshift n0 (scaleAux d (d * m) b)))

/-- `K < Σ_j b_j σ^j` for `σ ∈ [(n0 - 1)/2^d, (n0 + 1)/2^d]`, by bisection up to `fuel` more levels. -/
def polyOK (m : Nat) (b : List Int) (K : Nat) : Nat → Nat → Int → Bool
  | 0, d, n0 => nodeOK m b K d n0
  | f + 1, d, n0 => nodeOK m b K d n0 || (polyOK m b K f (d + 1) (2 * n0 - 1) && polyOK m b K f (d + 1) (2 * n0 + 1))

/-- `[t_0, t_1 e, t_2 e², …]`. -/
def scaleEta (P : Nat) (e : Ball) : List Ball → Ball → List Ball
  | [], _ => []
  | t :: ts, pw => mul P t pw :: scaleEta P e ts (mul P pw e)

/-! ## Pieces and segments -/

/-- The piece `[lo, lo + w] ⊆ [y₀ - η, y₀ + η]` (`y₀ = lo + ⌊w/2⌋`, `η = ⌈w/2⌉`): order-`m` Taylor model at `y₀`,
`|T_{m+1}|` bounded on the piece, omitted terms bounded by `R`, positivity by bisection (depth `dm`). -/
def pieceOK4 (P n k m dm : Nat) (gs : List PG4) (sps : List GSpec) (R : Nat) (lo : Int) (w : Nat) : Bool :=
  let η := w - w / 2
  let y0 := lo + ((w / 2 : Nat) : Int)
  match jetAll P m (expB' P n) (cosSinTurn P n k) ⟨y0, 0⟩ gs sps,
      jetAll P (m + 1) (expH P n) (cosSinTurnC P n k) ⟨y0, η⟩ gs sps with
  | some T, some T' =>
    let M := (T'.getD (m + 1) ⟨0, 0⟩).absHi
    let bs := scaleEta P ⟨η, 0⟩ T (ofInt P 1)
    let K := (bs.map (·.r)).sum + cdiv (M * η ^ (m + 1)) (2 ^ (P * (m + 1))) + R
    decide (T.length = m + 1) && polyOK m (bs.map (·.m)) K dm 0 0
  | _, _ => false

/-- `count` pieces of width `w` from `lo`. -/
def runOK (P n k m dm : Nat) (gs : List PG4) (sps : List GSpec) (R w : Nat) : Nat → Int → Bool
  | 0, _ => true
  | c + 1, lo => pieceOK4 P n k m dm gs sps R lo w && runOK P n k m dm gs sps R w c (lo + w)

/-- Pieces given as runs `(w, count)` from `lo`. -/
def runsOK (P n k m dm : Nat) (gs : List PG4) (sps : List GSpec) (R : Nat) : Int → List (Nat × Nat) → Bool
  | _, [] => true
  | lo, (w, c) :: rs => runOK P n k m dm gs sps R w c lo && runsOK P n k m dm gs sps R (lo + ((w * c : Nat) : Int)) rs

/-- The end of the runs from `lo`. -/
def runsEnd (lo : Int) (rs : List (Nat × Nat)) : Int := lo + ((rs.map fun r => r.1 * r.2).sum : Nat)

/-- A segment: start, Taylor order, included terms per group, runs of piece widths. -/
structure Seg4 where
  lo : Int
  m : Nat
  sps : List GSpec
  ws : List (Nat × Nat)
deriving Repr

/-- One segment of the range check (checker v4). -/
def segOK4 (c : Cfg) (gs : List GGroup) (s : Seg4) : Bool :=
  match prepGroups4 c.P c.n gs with
  | some pgs =>
    match omitAll c.P c.n s.lo (runsEnd s.lo s.ws) pgs s.sps with
    | some R => runsOK c.P c.n c.k s.m c.depth pgs s.sps R s.lo s.ws
    | none => false
  | none => false

end SignUnc.Chk
