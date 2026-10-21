import SUCert.LowData

/-!
# Checker for the lower-bound certificate (core Lean only)

`v = Σ c (b - b̂) + Σ d cos(2πβ·)`, `φ = 1 - v + ψ` on `I = [-r, r]`, `W = 1 - v + φ̂`, `ρ = φ̂ - ψ`.

* `pOK`: the pieces `P_k` (scaled Taylor polynomials, data) satisfy `|φ - P_k| ≤ ε` on their intervals
  (Taylor models of `φ` at the centres, remainder from an interval jet of order `D + 1`).
* `rhoOK`: `|ρ| ≤ δ` on `[0, r]`, from the moments of `P`: `P̂(x) - ψ(x) = Σ_n ρ_n x^(2n) + E_N(x)` and
  `|φ̂ - P̂| ≤ 2rε`.
* `lowPieceOK`: `W ≥ m` on a piece `[y₀ - η, y₀ + η]`: Taylor model of `1 - v + P̂` at `y₀` (jets of `v` from the
  group machinery of checker v4 with the cosine rows negated, cosine jets, jets of `P̂` from per-piece moments),
  remainders, positivity of the integer polynomial by bisection.
* `tailOK`: `W ≥ m` on `[Y, ∞)`, from the knot jumps of `P` (exact integration by parts of polynomials).
Soundness: `SignUnc.LowSound`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball

/-! ## The Gaussian part of `v` -/

/-- A group whose cosine rows carry `-c`: `groupJet` then gives the jets of `Σ c (b - b̂)`. -/
def prepGroupV (P n : Nat) (g : GGroup) : Option PG4 :=
  (prepGroup4 P n g).map fun G => ⟨G.G, G.OM.map fun x => (neg x.1, x.2.1, x.2.2)⟩

def prepGroupsV (P n : Nat) : List GGroup → Option (List PG4)
  | [] => some []
  | g :: L => (prepGroupV P n g).bind fun G => (prepGroupsV P n L).bind fun Gs => some (G :: Gs)

/-- All terms of every group. -/
def fullSpecs : List GGroup → List GSpec
  | [] => []
  | g :: L => ⟨0, g.cs.length, g.cs.length, true⟩ :: fullSpecs L

/-! ## Cosines and `ψ` -/

/-- Jets `[d cos θ, -d w sin θ, -d w² cos θ/2!, d w³ sin θ/3!, …]` of `d cos(2πβ(y+s))` in `s`
(`θ = 2πβy`, `w = 2πβ`); `q = (βn, βd, dn, dd)`. -/
def cosJet (P n : Nat) (cz : Ball → Option (Ball × Ball)) (Y : Ball) (q : Nat × Nat × Int × Nat) :
    Option (List Ball) :=
  (cz (mul P (ofRat P q.1 q.2.1) Y)).map fun cs =>
    divFact (pows2 P (neg (mul P (mul P (mulInt 2 (piB P)) (ofRat P q.1 q.2.1))
        (mul P (mulInt 2 (piB P)) (ofRat P q.1 q.2.1)))) (n + 1)
      (mul P (ofRat P q.2.2.1 q.2.2.2) cs.1)
      (neg (mul P (ofRat P q.2.2.1 q.2.2.2) (mul P (mul P (mulInt 2 (piB P)) (ofRat P q.1 q.2.1)) cs.2))))

def cosJets (P n : Nat) (cz : Ball → Option (Ball × Ball)) (Y : Ball) :
    List (Nat × Nat × Int × Nat) → Option (List Ball)
  | [] => some (zeroL (n + 1))
  | q :: L => (cosJet P n cz Y q).bind fun a => (cosJets P n cz Y L).bind fun b => some (addL a b)

/-- Taylor shift of a ball polynomial: coefficients of `p(y + s)` in `s` from those of `p(t)`. -/
def bshift (P : Nat) (y : Ball) : List Ball → List Ball
  | [] => []
  | c :: cs => List.zipWith add (c :: bshift P y cs) ((bshift P y cs).map (mul P y) ++ [⟨0, 0⟩])

/-- `ψ(t) = Σ_k q_k t^(2k)` as a ball polynomial `[q₀, 0, q₁, 0, …]`. -/
def psiPoly (P : Nat) : List (Int × Nat) → List Ball
  | [] => []
  | q :: L => ofRat P q.1 q.2 :: ⟨0, 0⟩ :: psiPoly P L

/-- The first `n` entries, padded with zero balls. -/
def padTake : Nat → List Ball → List Ball
  | 0, _ => []
  | n + 1, [] => ⟨0, 0⟩ :: padTake n []
  | n + 1, b :: bs => b :: padTake n bs

/-- Per-term jets `Σ c E e_j(α, β)` of Gaussian terms (rows `(c, s)`, values `E`, `α = -tpa (Y ∓ s)`); unlike the
moments of checker v4, no cancellation between powers of large `α` (needed for large widths and high orders). -/
def termE (P n : Nat) (tpa be Y : Ball) (sgn : Bool) : List (Ball × Ball) → List Ball → List Ball
  | (C, s) :: cs, E :: es =>
    addL ((eser P n (neg (mul P tpa (if sgn then add Y s else sub Y s))) be).map (mul P (mul P C E)))
      (termE P n tpa be Y sgn cs es)
  | _, _ => zeroL (n + 1)

/-- `[T_0, …, T_n]` of the included terms of a group at `Y` (per-term Gaussian jets, cosine moments). -/
def groupJetT (P n : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (G : PG4) (sp : GSpec)
    (Y : Ball) : Option (List Ball) :=
  (gridE P ex G.G Y sp.k1 sp.k2).bind fun Es =>
  (gridF P ex G.G Y sp.kF).bind fun Fs =>
    let tE := addL (termE P n (mulInt 2 G.G.pa) (neg G.G.pa) Y false (G.G.CS.drop sp.k1) Es)
      (termE P n (mulInt 2 G.G.pa) (neg G.G.pa) Y true G.G.CS Fs)
    if sp.hz then
      (gridH P ex cz G.G Y).bind fun HZ =>
        let gH := eser P n (neg (mul P (mulInt 2 (piB P)) (mul P Y G.G.Ai))) (neg (mul P (piB P) G.G.Ai))
        some (addL tE ((conv P gH (divFact (momH P n G.OM HZ.2))).map (mul P HZ.1)))
    else some tE

def jetAllT (P n : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (Y : Ball) :
    List PG4 → List GSpec → Option (List Ball)
  | [], [] => some (zeroL (n + 1))
  | G :: Gs, sp :: sps =>
    (groupJetT P n ex cz G sp Y).bind fun a => (jetAllT P n ex cz Y Gs sps).bind fun b => some (addL a b)
  | _, _ => none

/-- Jets of `v = Σ c (b - b̂) + Σ d cos` (included Gaussian terms) at `Y`. -/
def vJet (P n : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (gs : List PG4)
    (sps : List GSpec) (cos : List (Nat × Nat × Int × Nat)) (Y : Ball) : Option (List Ball) :=
  (jetAllT P n ex cz Y gs sps).bind fun a => (cosJets P n cz Y cos).bind fun b => some (addL a b)

/-- Jets of `φ = 1 - v + ψ` (all terms) at `Y`. -/
def phiJet (P n : Nat) (ex : Ball → Option Ball) (cz : Ball → Option (Ball × Ball)) (gs : List PG4)
    (sps : List GSpec) (cos : List (Nat × Nat × Int × Nat)) (psi : List Ball) (Y : Ball) : Option (List Ball) :=
  (vJet P n ex cz gs sps cos Y).map fun v =>
    List.zipWith sub (List.zipWith add (ofInt P 1 :: zeroL n) (padTake (n + 1) (bshift P Y psi))) v

/-! ## The approximant `P` -/

/-- A piece `(lo, hi, B)`: `[lo/10000, hi/10000]`, `P(c + ησ) = Σ_i B_i 2^-P σ^i`. -/
abbrev PPiece := Nat × Nat × List Int

def pcen (P : Nat) (pc : PPiece) : Ball := ofRat P ((pc.1 + pc.2.1 : Nat) : Int) 20000
def peta (P : Nat) (pc : PPiece) : Ball := ofRat P ((pc.2.1 - pc.1 : Nat) : Int) 20000

/-- `x^n` for a ball. -/
def powB (P : Nat) (x : Ball) : Nat → Ball
  | 0 => ofInt P 1
  | n + 1 => mul P (powB P x n) x

/-- `[t_0, t_1 w/d, t_2 (w/d)², …]` with exact integer powers and one rounding per entry (fixed point cannot hold
tiny powers `(w/d)^j`). -/
def scaleRatAux (w d : Nat) : Nat → List Ball → List Ball
  | _, [] => []
  | j, t :: ts => divNat (d ^ j) (mulInt ((w ^ j : Nat) : Int) t) :: scaleRatAux w d (j + 1) ts

def scaleRat (w d : Nat) (T : List Ball) : List Ball := scaleRatAux w d 0 T

/-- `|φ - P_k| ≤ ε` on the piece (`eps`, `R` in units `2^-P`; `R` bounds the omitted Gaussian terms): point jets of
`φ` of order `D + L` at the centre (entries `≤ D` matched with `P_k`, entries `> D` bounded by their absolute values),
interval jet of order `D + L + 1` on the piece for the remainder. -/
def pieceP_OK (P n k D L : Nat) (gs : List PG4) (sps : List GSpec) (cos : List (Nat × Nat × Int × Nat))
    (psi : List Ball) (eps R : Nat) (pc : PPiece) : Bool :=
  let C := pcen P pc
  let E := peta P pc
  let w := pc.2.1 - pc.1
  match phiJet P (D + L) (expB' P n) (cosSinTurn P n k) gs sps cos psi C,
      phiJet P (D + L + 1) (expH P n) (cosSinTurnC P n k) gs sps cos psi ⟨C.m, C.r + E.m.natAbs + E.r⟩ with
  | some T, some T' =>
    let bs := scaleRat w 20000 T
    let S1 := ((List.zipWith (fun b B => sub b ⟨B, 0⟩) bs pc.2.2).map absHi).sum
    let S2 := ((bs.drop (D + 1)).map absHi).sum
    let rem := (divNat (20000 ^ (D + L + 1))
      (mulInt ((w ^ (D + L + 1) : Nat) : Int) (absB (T'.getD (D + L + 1) ⟨0, 0⟩)))).absHi
    decide (pc.1 < pc.2.1) && decide (T.length = D + L + 1) && decide (pc.2.2.length = D + 1) &&
      decide (S1 + S2 + rem + R ≤ eps)
  | _, _ => false

/-- The pieces cover `[a/10000, 5502/10000]` contiguously. -/
def chainOK : Nat → List PPiece → Bool
  | a, [] => decide (a = 5502)
  | a, pc :: L => decide (pc.1 = a) && chainOK pc.2.1 L

/-- One piece with its included terms: the omitted terms are bounded on `[lo/10000, hi/10000]`. -/
def pieceP_OK' (P n k D L : Nat) (pgs : List PG4) (cos : List (Nat × Nat × Int × Nat)) (psi : List Ball)
    (eps : Nat) (x : PPiece × List GSpec) : Bool :=
  match omitAll P n ((x.1.1 * 2 ^ P / 10000 : Nat) : Int) (((x.1.2.1 * 2 ^ P + 9999) / 10000 : Nat) : Int) pgs x.2 with
  | some R => pieceP_OK P n k D L pgs x.2 cos psi eps R x.1
  | none => false

def pOK (P n k D L : Nat) (gs : List GGroup) (cos : List (Nat × Nat × Int × Nat)) (psi : List (Int × Nat))
    (eps : Nat) (ps : List PPiece) (sps : List (List GSpec)) : Bool :=
  match prepGroupsV P n gs with
  | some pgs => chainOK 0 ps && decide (ps.length = sps.length) &&
      (ps.zip sps).all (pieceP_OK' P n k D L pgs cos (psiPoly P psi) eps)
  | none => false

/-- `max_k Σ_i |B_i|` (units `2^-P`): a bound of `|P|` on `[0, r]`. -/
def pmaxHi (ps : List PPiece) : Nat := ps.foldr (fun pc acc => max ((pc.2.2.map Int.natAbs).sum) acc) 0

/-! ## Moments of `P` -/

/-- `q(σ) (c + η σ)`. -/
def mulLin (P : Nat) (c e : Ball) (q : List Ball) : List Ball :=
  List.zipWith add (q.map (mul P c) ++ [⟨0, 0⟩]) (⟨0, 0⟩ :: q.map (mul P e))

/-- `∫_{-1}^{1} σ^e (Σ_i q_i σ^i) σ^n dσ` summed over the list from index `e` (`2/(e+i+n+1)` for even
`e + i + n`). -/
def intPowAux (n : Nat) : Nat → List Ball → Ball
  | _, [] => ⟨0, 0⟩
  | e, b :: bs => if (e + n) % 2 = 0 then add (divNat (e + n + 1) (mulInt 2 b)) (intPowAux n (e + 1) bs)
      else intPowAux n (e + 1) bs

/-- `∫_{-1}^{1} q(σ) σ^n dσ`. -/
def intPow (q : List Ball) (n : Nat) : Ball := intPowAux n 0 q

/-- `[∫ q, ∫ q (c+ησ), ∫ q (c+ησ)², …]` (`N` entries). -/
def momLin (P : Nat) (c e : Ball) : Nat → List Ball → List Ball
  | 0, _ => []
  | N + 1, q => intPow q 0 :: momLin P c e N (mulLin P c e q)

/-- The scaled coefficients of a piece as exact balls. -/
def pcoef (pc : PPiece) : List Ball := pc.2.2.map fun B => ⟨B, 0⟩

/-- `μ_j = 2 Σ_k η_k ∫_{-1}^{1} p_k(σ) (c_k + η_k σ)^j dσ = ∫_{-r}^{r} P(t) t^j dt`, `j < J`. -/
def momAll (P J : Nat) : List PPiece → List Ball
  | [] => zeroL J
  | pc :: L => addL ((momLin P (pcen P pc) (peta P pc) J (pcoef pc)).map fun m => mulInt 2 (mul P (peta P pc) m))
      (momAll P J L)

/-- `ρ_n = (-1)^n (2π)^(2n) μ_(2n) / (2n)! - q_n` for `n < N` (from `[μ_0, μ_1, …]`, `q` padded). -/
def rhoCoefAux (P : Nat) (tp2 : Ball) : Nat → Ball → List Ball → List Ball → List Ball
  | _, _, [], _ => []
  | n, fac, [m0], qs => [sub (mul P fac m0) (qs.headD ⟨0, 0⟩)]
  | n, fac, m0 :: _ :: ms, qs =>
    sub (mul P fac m0) (qs.headD ⟨0, 0⟩) ::
      rhoCoefAux P tp2 (n + 1) (divNat ((2 * n + 1) * (2 * n + 2)) (neg (mul P fac tp2))) ms qs.tail

/-- `|ρ| ≤ δ` on `[0, r]` (`δ`, `ε` in units `2^-P`): `Σ_(n<N) |ρ_n| r^(2n) + E_N + 2rε ≤ δ`. -/
def rhoOK (P N : Nat) (psi : List (Int × Nat)) (ps : List PPiece) (eps delta : Nat) : Bool :=
  let r := ofRat P 2751 5000
  let r2 := mul P r r
  let tp2 := mul P (mulInt 2 (piB P)) (mulInt 2 (piB P))
  let rhos := rhoCoefAux P tp2 0 (ofInt P 1) (momAll P (2 * N) ps) (psi.map fun q => ofRat P q.1 q.2)
  let S := (rhos.zipWith (fun b p => (mul P (absB b) p).absHi) ((List.range N).map (powB P r2))).sum
  -- E_N ≤ ∫|P| |2πxt|^(2N)/(2N)! ≤ 2r Pmax (2π r²)^(2N) / (2N)!
  let EN := (mul P (mul P (mulInt 2 r) ⟨(pmaxHi ps : Int), 0⟩)
    (divNat (fact (2 * N)) (powB P (mul P (mulInt 2 (piB P)) r2) (2 * N)))).absHi
  let twoReps := (mul P (mulInt 2 r) ⟨(eps : Int), 0⟩).absHi
  decide (psi.length ≤ N) && decide (rhos.length = N) && decide (S + EN + twoReps ≤ delta)

/-! ## Jets of `P̂` in `y` -/

def pieceMomsAux (P N : Nat) (c e : Ball) : Nat → List Ball → List (List Ball)
  | 0, _ => []
  | M + 1, q => (List.range N).map (intPow q) :: pieceMomsAux P N c e M (mulLin P c e q)

/-- For one piece: `μ_{j,n} = ∫_{-1}^{1} p(σ) (c + ησ)^j σ^n dσ` for `j ≤ M`, `n < N`. -/
def pieceMoms (P M N : Nat) (pc : PPiece) : List (List Ball) :=
  pieceMomsAux P N (pcen P pc) (peta P pc) (M + 1) (pcoef pc)

/-- `Σ_i |B_i|` of one piece. -/
def pmaxOne (pc : PPiece) : Nat := (pc.2.2.map Int.natAbs).sum

/-- `(Σ_n i^n a_n μ_n)` as `(X, Y)` (real and imaginary parts), with `a_n = x^n/n!`. -/
def seriesIA (P : Nat) (x : Ball) : Nat → Ball → List Ball → Ball × Ball
  | _, _, [] => (⟨0, 0⟩, ⟨0, 0⟩)
  | n, a, m :: ms =>
    let rest := seriesIA P x (n + 1) (divNat (n + 1) (mul P a x)) ms
    let t := mul P a m
    match n % 4 with
    | 0 => (add t rest.1, rest.2)
    | 1 => (rest.1, add t rest.2)
    | 2 => (sub rest.1 t, rest.2)
    | _ => (rest.1, sub rest.2 t)

/-- Jets `[P̂_0, …, P̂_M]` of `P̂(y) = 2 Re ∫_0^r P(t) e^{2πiyt} dt` at the point ball `Y0`, with the truncation
error of the series in `n < N` added to the radii. -/
def phatJet (P n k M N : Nat) (ps : List PPiece) (moms : List (List (List Ball))) (pmaxs : List Nat) (Y0 : Ball) :
    Option (List Ball) :=
  let w := mul P (mulInt 2 (piB P)) Y0
  let r := ofRat P 2751 5000
  let terms : List (Option (List Ball)) := (ps.zip (moms.zip pmaxs)).map fun x =>
    let pc := x.1
    let mk := x.2.1
    let c := pcen P pc
    let e := peta P pc
    (cosSinTurn P n k (mul P Y0 c)).map fun cs =>
      let we := mul P w e
      -- truncation error per unit: 2 (|w e|)^N / N! (real and imaginary parts) times ∫|q_j| ≤ 2 pmax r^j
      let tr := divNat (fact N) (mulInt 2 (powB P ⟨(we.absHi : Int), 0⟩ N))
      (List.range (M + 1)).zipWith (fun j mj =>
        let XY := seriesIA P we 0 (ofInt P 1) mj
        let U := sub (mul P cs.1 XY.1) (mul P cs.2 XY.2)
        let V := add (mul P cs.2 XY.1) (mul P cs.1 XY.2)
        let base : Ball := match j % 4 with
          | 0 => U
          | 1 => neg V
          | 2 => neg U
          | _ => V
        let fac := divNat (fact j) (powB P (mulInt 2 (piB P)) j)
        let val := mulInt 2 (mul P fac (mul P e base))
        let err := (mul P (mulInt 4 (mul P fac (mul P e ⟨(x.2.2 : Int), 0⟩))) (mul P (powB P r j) tr)).absHi
        (⟨val.m, val.r + err⟩ : Ball)) mk
  terms.foldr (fun t acc => t.bind fun a => acc.bind fun b => some (addL a b)) (some (zeroL (M + 1)))

/-- `4 r Pmax (2π r η)^(M+1) / (M+1)!` (units `2^-P`): the remainder of `P̂` in `y` over `|s| ≤ η` (the factor 2
covers the real and imaginary parts of the remainder of `e^{iθ}`). -/
def phatRem (P M pmax : Nat) (eta : Nat) : Nat :=
  let r := ofRat P 2751 5000
  (mul P (mul P (mulInt 4 r) ⟨(pmax : Int), 0⟩)
    (divNat (fact (M + 1)) (powB P (mul P (mul P (mulInt 2 (piB P)) r) ⟨(eta : Int), 0⟩) (M + 1)))).absHi

/-! ## Pieces in `y` -/

/-- `W ≥ m` on `[lo, lo + w] ⊆ [y₀ - η, y₀ + η]` from the Taylor model of `1 - v + P̂` of order `M`
(`R`: omitted Gaussian terms, `base = m + 2rε`, both in units `2^-P`). -/
def lowPieceOK (P n k M N dm : Nat) (gs : List PG4) (sps : List GSpec) (cos : List (Nat × Nat × Int × Nat))
    (ps : List PPiece) (moms : List (List (List Ball))) (pmax : Nat) (R base : Nat) (lo : Int) (w : Nat) : Bool :=
  let η := w - w / 2
  let y0 := lo + ((w / 2 : Nat) : Int)
  match vJet P M (expB' P n) (cosSinTurn P n k) gs sps cos ⟨y0, 0⟩,
      vJet P (M + 1) (expH P n) (cosSinTurnC P n k) gs sps cos ⟨y0, η⟩,
      phatJet P n k M N ps moms (ps.map pmaxOne) ⟨y0, 0⟩ with
  | some V, some V', some H =>
    let T := List.zipWith add (List.zipWith sub (ofInt P 1 :: zeroL M) V) H
    let remv := cdiv ((V'.getD (M + 1) ⟨0, 0⟩).absHi * η ^ (M + 1)) (2 ^ (P * (M + 1)))
    let bs := scaleRat η (2 ^ P) T
    let K := (bs.map (·.r)).sum + remv + phatRem P M pmax η + R + base
    decide (T.length = M + 1) && polyOK M (bs.map (·.m)) K dm 0 0
  | _, _, _ => false

def lrunOK (P n k M N dm : Nat) (gs : List PG4) (sps : List GSpec) (cos : List (Nat × Nat × Int × Nat))
    (ps : List PPiece) (moms : List (List (List Ball))) (pmax R base w : Nat) : Nat → Int → Bool
  | 0, _ => true
  | c + 1, lo => lowPieceOK P n k M N dm gs sps cos ps moms pmax R base lo w &&
      lrunOK P n k M N dm gs sps cos ps moms pmax R base w c (lo + w)

def lrunsOK (P n k M N dm : Nat) (gs : List PG4) (sps : List GSpec) (cos : List (Nat × Nat × Int × Nat))
    (ps : List PPiece) (moms : List (List (List Ball))) (pmax R base : Nat) : Int → List (Nat × Nat) → Bool
  | _, [] => true
  | lo, (w, c) :: rs => lrunOK P n k M N dm gs sps cos ps moms pmax R base w c lo &&
      lrunsOK P n k M N dm gs sps cos ps moms pmax R base (lo + ((w * c : Nat) : Int)) rs

/-- A segment in `y`: start, Taylor order `M`, series length `N`, included Gaussian terms, piece runs. -/
structure LSeg where
  lo : Int
  M : Nat
  N : Nat
  sps : List GSpec
  ws : List (Nat × Nat)
deriving Repr

/-- Parameters of the lower check (`m`, `ε`, `δ` in units `2^-P`). -/
structure LCfg where
  P : Nat
  n : Nat
  k : Nat
  D : Nat
  L : Nat
  dm : Nat
  m : Nat
  eps : Nat
  delta : Nat
  Nrho : Nat
  YT : Nat
deriving Repr

def lsegOK (c : LCfg) (gs : List GGroup) (cos : List (Nat × Nat × Int × Nat)) (ps : List PPiece) (s : LSeg) : Bool :=
  match prepGroupsV c.P c.n gs with
  | some pgs =>
    match omitAll c.P c.n s.lo (runsEnd s.lo s.ws) pgs s.sps with
    | some R =>
      lrunsOK c.P c.n c.k s.M s.N c.dm pgs s.sps cos ps (ps.map (pieceMoms c.P s.M s.N)) (pmaxHi ps) R
        (c.m + (mul c.P (mulInt 2 (ofRat c.P 2751 5000)) ⟨(c.eps : Int), 0⟩).absHi) s.lo s.ws
    | none => false
  | none => false

/-! ## The tail `y ≥ Y` -/

/-- `Σ_{i ≥ l} B_i i!/(i-l)! (±1)^(i-l)` (`sgn = true`: `σ = -1`), the `l`-th derivative of `p` at `σ = ±1`. -/
def derivPM (bs : List Int) (l : Nat) (sgn : Bool) : Int :=
  ((List.range bs.length).zip bs).foldr (fun ib acc =>
    if l ≤ ib.1 then
      acc + ib.2 * ((fact ib.1 / fact (ib.1 - l) : Nat) : Int) *
        (if sgn && (ib.1 - l) % 2 = 1 then -1 else 1)
    else acc) 0

/-- The jump of `P^(l)` at a knot, times `ω^-(l+1)`, as a ball: `(S₁ w₁^-l - S₂ w₂^-l) 20000^l / ω^(l+1)` with
`ω ≥ 2 · 3.141592 · Y` (units `2^-P`; `S` in units `2^-P`, widths `w` in units `1/10000`). -/
def jumpTerm (P YT l : Nat) (S1 : Int) (w1 : Nat) (S2 : Int) (w2 : Nat) : Nat :=
  let num : Int := (S1 * ((w2 ^ l : Nat) : Int) - S2 * ((w1 ^ l : Nat) : Int)) * ((20000 ^ l * 1000000 ^ (l + 1) : Nat) : Int)
  let den : Nat := (w1 * w2) ^ l * (2 * 3141592 * YT) ^ (l + 1) * 2 ^ P
  (ofRat P num.natAbs den).absHi

/-- `Σ_l` over the knots of `[0, r]`; knot `0` and knot `r` have one side only. -/
def jumpsAll (P YT D : Nat) : Nat × Int × List Int → List PPiece → Nat
  | _, [] => 0
  | (wprev, _, bprev), pc :: L =>
    (List.range (D + 1)).foldr (fun l acc => acc +
      -- at the knot `0` only odd `l` contribute to the real part (`Re (iω)^-(l+1) = 0` for even `l`)
      if wprev = 0 ∧ l % 2 = 0 then 0 else
      jumpTerm P YT l (if wprev = 0 then 0 else derivPM bprev l false) (if wprev = 0 then 1 else wprev)
        (derivPM pc.2.2 l true) (pc.2.1 - pc.1)) 0 +
    jumpsAll P YT D (pc.2.1 - pc.1, 0, pc.2.2) L

/-- The right end `r`: the last piece at `σ = 1`. -/
def jumpsEnd (P YT D : Nat) (ps : List PPiece) : Nat :=
  match ps.getLast? with
  | some pc => (List.range (D + 1)).foldr (fun l acc => acc + jumpTerm P YT l (derivPM pc.2.2 l false)
      (pc.2.1 - pc.1) 0 1) 0
  | none => 0

/-- `Σ_k |c_k| (2 e^{-πa(Y - s_max)²} + Q e^{-πY²/a})` over the groups (units `2^-P`), for `Y ≥ s_max`. -/
def vGtail (P n : Nat) (YT : Nat) : List PG4 → Option Nat
  | [] => some 0
  | G :: L =>
    let smax := ofRat P (G.G.g.sk (G.G.g.cs.length - 1)).1 (G.G.g.sk (G.G.g.cs.length - 1)).2
    let Yb := ofInt P (YT : Int)
    let D := sub Yb smax
    if D.isPos then
      (expB' P n (neg (mul P G.G.pa (mul P D D)))).bind fun e1 =>
      (expB' P n (neg (mul P (piB P) (mul P (mul P Yb Yb) G.G.Ai)))).bind fun e2 =>
      (vGtail P n YT L).bind fun rest =>
        some (cdiv ((add (mulInt 2 e1) (mul P G.G.Q e2)).absHi * csumHi G.G) (2 ^ P) + rest)
    else none

/-- `W ≥ m` on `[Y, ∞)`: `1 - Σ d - vG - 2(jumps) - 2rε > m` (all bounds decreasing in `y`). -/
def ltailOK (c : LCfg) (gs : List GGroup) (cos : List (Nat × Nat × Int × Nat)) (ps : List PPiece) : Bool :=
  match prepGroupsV c.P c.n gs, cos.all (fun q => decide (0 ≤ q.2.2.1)) with
  | some pgs, true =>
    match vGtail c.P c.n c.YT pgs with
    | some vg =>
      let dsum := ((cos.map fun q => ofRat c.P q.2.2.1 q.2.2.2).foldr add ⟨0, 0⟩).absHi
      let J := jumpsAll c.P c.YT c.D (0, 0, []) ps + jumpsEnd c.P c.YT c.D ps
      let twoReps := (mul c.P (mulInt 2 (ofRat c.P 2751 5000)) ⟨(c.eps : Int), 0⟩).absHi
      decide (dsum + vg + 2 * J + twoReps + c.m < 2 ^ c.P)
    | none => false
  | _, _ => false

/-! ## The whole check except the segments -/

/-- The end of a contiguous chain of segments from `lo` (non-empty runs, positive widths and counts). -/
def lcontigEnd : Int → List LSeg → Option Int
  | lo, [] => some lo
  | lo, s :: ss =>
    if s.lo = lo ∧ s.ws ≠ [] ∧ s.ws.all (fun r => decide (0 < r.1) && decide (0 < r.2)) = true then
      lcontigEnd (runsEnd s.lo s.ws) ss
    else none

/-- `P` is `ε`-close to `φ`, `|ρ| ≤ δ`, the segments cover `[⌊r 2^P⌋, Y]`, the tail check at `Y`. -/
def lbaseOK (c : LCfg) (gs : List GGroup) (cos : List (Nat × Nat × Int × Nat)) (psi : List (Int × Nat))
    (ps : List PPiece) (pss : List (List GSpec)) (segs : List LSeg) : Bool :=
  pOK c.P c.n c.k c.D c.L gs cos psi c.eps ps pss && rhoOK c.P c.Nrho psi ps c.eps c.delta &&
  ltailOK c gs cos ps &&
  match lcontigEnd ((2751 * 2 ^ c.P / 5000 : Nat) : Int) segs with
  | some e => decide (((c.YT * 2 ^ c.P : Nat) : Int) ≤ e)
  | none => false

end SignUnc.Chk
