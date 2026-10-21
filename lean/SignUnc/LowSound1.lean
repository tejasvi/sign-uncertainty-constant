import SignUnc.PieceSound
import SUCert.Low

/-!
# Soundness of the lower checker, part 1: jets of `v` (signed Gaussian pairs, cosines) and of `ψ`

`v = Σ c (b - b̂) + Σ d cos(2πβ·)`: the E- and mirror terms as in checker v4, the cosine rows of each group with
`-c` (`inclHV`), the cosines as quadratic exponentials with `B = 0` (`quadC`).  Gaussian terms per term
(`termE`, no moments).  `ψ` (any polynomial): Taylor coefficients by synthetic division (`Tpoly`).
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex Finset

variable {P : ℕ}

/-! ## Signed terms of `v` -/

noncomputable def inclHV (g : GGroup) (sp : GSpec) : List (ℂ × ℂ × ℂ × ℂ) :=
  if sp.hz then g.csR.map fun r => quadH (aR g) (-r.1) r.2 else []

noncomputable def inclV (g : GGroup) (sp : GSpec) : List (ℂ × ℂ × ℂ × ℂ) := inclE g sp ++ inclF g sp ++ inclHV g sp

noncomputable def inclAllV : List GGroup → List GSpec → List (ℂ × ℂ × ℂ × ℂ)
  | g :: gs, sp :: sps => inclV g sp ++ inclAllV gs sps
  | _, _ => []

/-- Real rows of the cosine moments with `-c`. -/
noncomputable def rowsHV (g : GGroup) (y : ℝ) : List (ℝ × ℝ × ℝ) :=
  g.csR.map fun r => (-r.1 * Real.cos (2 * π * r.2 * y), -((2 * π * r.2) * (-r.1 * Real.sin (2 * π * r.2 * y))),
    -((2 * π * r.2) * (2 * π * r.2)))

theorem tauSum_inclHV_hz (g : GGroup) (sp : GSpec) (hz : sp.hz = true) (j : ℕ) (y : ℝ) :
    tauSum (inclHV g sp) j y = 2 / Real.sqrt (aR g) * Real.exp (-π * y ^ 2 / aR g) *
      ∑ p ∈ range (j + 1), momR2 (rowsHV g y) p / (p.factorial : ℝ) *
        ecoef (-(2 * π * (y * (1 / aR g)))) (-(π * (1 / aR g))) (j - p) := by
  rw [← listSum_pw2, ← List.sum_map_mul_left]
  unfold inclHV
  rw [if_pos hz, tauSum_eq, rowsHV, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply]
  rw [tau_quadH]

theorem tauSum_inclHV_nhz (g : GGroup) (sp : GSpec) (hz : sp.hz = false) (j : ℕ) (y : ℝ) :
    tauSum (inclHV g sp) j y = 0 := by
  unfold inclHV; rw [if_neg (by simp [hz])]; simp [tauSum]

theorem tauSum_inclV (g : GGroup) (sp : GSpec) (j : ℕ) (y : ℝ) :
    tauSum (inclV g sp) j y = tauSum (inclE g sp) j y + tauSum (inclF g sp) j y + tauSum (inclHV g sp) j y := by
  rw [inclV, tauSum_append, tauSum_append]

/-! ## Groups with negated cosine rows -/

structure PGVOk (P : ℕ) (G : PG4) : Prop where
  hG : PGOk P G.G
  hOM : List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball × Ball) =>
    mem P (-r.1) b.1 ∧ mem P (2 * π * r.2) b.2.1 ∧ mem P (-((2 * π * r.2) * (2 * π * r.2))) b.2.2) G.G.g.csR G.OM

theorem prepGroupV_ok {n : ℕ} {g : GGroup} {G : PG4} (h : prepGroupV P n g = some G) : PGVOk P G ∧ G.G.g = g := by
  unfold prepGroupV at h
  obtain ⟨G4, hG4, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hok, hg⟩ := prepGroup4_ok hG4
  refine ⟨⟨hok.hG, ?_⟩, hg⟩
  rw [List.forall₂_map_right_iff]
  exact hok.hOM.imp (fun r b hrb => ⟨mem_neg hrb.1, hrb.2.1, hrb.2.2⟩)

theorem prepGroupsV_ok {n : ℕ} : ∀ {L : List GGroup} {pgs : List PG4}, prepGroupsV P n L = some pgs →
    List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) L pgs
  | [], pgs, h => by simp [prepGroupsV] at h; subst h; exact List.Forall₂.nil
  | g :: L, pgs, h => by
    simp only [prepGroupsV, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨G, hG, Gs, hGs, rfl⟩ := h
    exact List.Forall₂.cons (prepGroupV_ok hG) (prepGroupsV_ok hGs)

/-! ## Per-term Gaussian jets -/

theorem memL_termE {n : ℕ} {tpa be Y : Ball} {tp b y : ℝ} (htpa : mem P tp tpa) (hbe : mem P b be)
    (hY : mem P y Y) (sgn : Bool) :
    ∀ {rs : List (ℝ × ℝ)} {RB : List (Ball × Ball)} {es : List ℝ} {EB : List Ball},
      List.Forall₂ (fun (r : ℝ × ℝ) (B : Ball × Ball) => mem P r.1 B.1 ∧ mem P r.2 B.2) rs RB → MemL P es EB →
      MemL P ((List.range (n + 1)).map fun j =>
        (List.zipWith (fun r e => r.1 * e * ecoef (-(tp * (if sgn then y + r.2 else y - r.2))) b j) rs es).sum)
        (termE P n tpa be Y sgn RB EB)
  | [], [], es, EB, List.Forall₂.nil, _ => by
    have e : (fun j => (List.zipWith (fun (r : ℝ × ℝ) (e : ℝ) =>
        r.1 * e * ecoef (-(tp * (if sgn then y + r.2 else y - r.2))) b j) [] es).sum) = fun _ => 0 := by
      funext j; simp
    rw [e]
    cases EB <;> exact memL_zeroL (n + 1)
  | _ :: _, _ :: _, [], [], List.Forall₂.cons _ _, List.Forall₂.nil => by
    rename_i x xs B RB _ _
    obtain ⟨C, s⟩ := B
    have e : (fun j => (List.zipWith (fun (r : ℝ × ℝ) (e : ℝ) =>
        r.1 * e * ecoef (-(tp * (if sgn then y + r.2 else y - r.2))) b j) (x :: xs) []).sum) = fun _ => 0 := by
      funext j; simp
    rw [e]; exact memL_zeroL (n + 1)
  | x :: xs, B :: RB, e :: es, E :: EB, List.Forall₂.cons hx hxs, List.Forall₂.cons he hes => by
    obtain ⟨C, s⟩ := B
    simp only [termE]
    have hα : mem P (-(tp * (if sgn then y + x.2 else y - x.2)))
        (neg (mul P tpa (if sgn then add Y s else sub Y s))) := by
      cases sgn
      · exact mem_neg (mem_mul htpa (mem_sub hY hx.2))
      · exact mem_neg (mem_mul htpa (mem_add hY hx.2))
    have h1 := memL_map_mul (mem_mul hx.1 he) (memL_eser hα hbe n)
    have h2 := memL_termE (n := n) htpa hbe hY sgn hxs hes
    have := memL_addL h1 h2
    rw [List.map_map, zipWith_add_range] at this
    convert this using 2
    funext j
    simp only [List.zipWith_cons_cons, List.sum_cons, Function.comp_apply]

theorem tauSum_inclE_term (g : GGroup) (sp : GSpec) (j : ℕ) (y : ℝ) :
    tauSum (inclE g sp) j y = (((g.csR.drop sp.k1).take (sp.k2 - sp.k1)).map fun r =>
      r.1 * Real.exp (-π * aR g * (y - r.2) ^ 2) * ecoef (-(2 * (π * aR g) * (y - r.2))) (-(π * aR g)) j).sum := by
  rw [tauSum_eq, inclE, List.map_map]
  congr 1
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply]
  rw [tau_quadE]; ring_nf

theorem tauSum_inclF_term (g : GGroup) (sp : GSpec) (j : ℕ) (y : ℝ) :
    tauSum (inclF g sp) j y = ((g.csR.take sp.kF).map fun r =>
      r.1 * Real.exp (-π * aR g * (y + r.2) ^ 2) * ecoef (-(2 * (π * aR g) * (y + r.2))) (-(π * aR g)) j).sum := by
  rw [tauSum_eq, inclF, List.map_map]
  congr 1
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply]
  rw [tau_quadF]; ring_nf

theorem groupJetT_ok {n : ℕ} {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {G : PG4} (hG : PGVOk P G) {y : ℝ} {Y : Ball} (hY : mem P y Y) {sp : GSpec} {T : List Ball}
    (h : groupJetT P n ex cz G sp Y = some T) :
    MemL P ((List.range (n + 1)).map fun j => tauSum (inclV G.G.g sp) j y) T := by
  have hPG := hG.hG
  set g := G.G.g with hgdef
  set a := aR g
  unfold groupJetT at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨Es, hEs, Fs, hFs, h⟩ := h
  obtain ⟨hEl, hE⟩ := gridE_ok hex hPG hY hEs
  obtain ⟨hFl, hF⟩ := gridF_ok hex hPG hY hFs
  have htpa : mem P (2 * (π * a)) (mulInt 2 G.G.pa) := by
    have := mem_mulInt 2 hPG.hpa; push_cast at this; exact this
  have hbe : mem P (-(π * a)) (neg G.G.pa) := mem_neg hPG.hpa
  -- E terms
  have htE : MemL P ((List.range (n + 1)).map fun j => tauSum (inclE g sp) j y)
      (termE P n (mulInt 2 G.G.pa) (neg G.G.pa) Y false (G.G.CS.drop sp.k1) Es) := by
    have hEs' : MemL P ((List.range (sp.k2 - sp.k1)).map fun i => Real.exp (-π * a * (y - sR g (sp.k1 + i)) ^ 2)) Es :=
      memL_of_getElem hEl hE
    have h1 := memL_termE (n := n) htpa hbe hY false (forall₂_drop sp.k1 hPG.hCS) hEs'
    convert h1 using 2
    funext j
    rw [tauSum_inclE_term]
    have heq := zipWith_range_eq (g.csR.drop sp.k1) (fun i => sR g (sp.k1 + i)) (csR_drop_snd g sp.k1)
      (fun s => Real.exp (-π * a * (y - s) ^ 2))
      (fun r e => r.1 * e * ecoef (-(2 * (π * a) * (if false then y + r.2 else y - r.2))) (-(π * a)) j) (sp.k2 - sp.k1)
    rw [heq]
    simp only [Bool.false_eq_true, if_false]
    rfl
  -- F terms
  have htF : MemL P ((List.range (n + 1)).map fun j => tauSum (inclF g sp) j y)
      (termE P n (mulInt 2 G.G.pa) (neg G.G.pa) Y true G.G.CS Fs) := by
    have hFs' : MemL P ((List.range sp.kF).map fun i => Real.exp (-π * a * (y + sR g i) ^ 2)) Fs :=
      memL_of_getElem hFl hF
    have h1 := memL_termE (n := n) htpa hbe hY true hPG.hCS hFs'
    convert h1 using 2
    funext j
    rw [tauSum_inclF_term]
    have heq := zipWith_range_eq g.csR (fun i => sR g i) (csR_snd g)
      (fun s => Real.exp (-π * a * (y + s) ^ 2))
      (fun r e => r.1 * e * ecoef (-(2 * (π * a) * (if true then y + r.2 else y - r.2))) (-(π * a)) j) sp.kF
    rw [heq]
    simp only [if_true]
    rfl
  have hEF := memL_addL htE htF
  rw [zipWith_add_range] at hEF
  cases hzc : sp.hz with
  | false =>
    rw [hzc] at h
    simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
    subst h
    convert hEF using 2
    funext j
    rw [tauSum_inclV, tauSum_inclHV_nhz g sp hzc, add_zero]
  | true =>
    rw [hzc] at h
    simp only [if_true, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨QH, Zs⟩, hHZ, rfl⟩ := h
    obtain ⟨hQH, hZl, hZ⟩ := gridH_ok hex hcz hPG hY hHZ
    have hZs : List.Forall₂ (fun (r : ℝ × ℝ) (Z : CDisc) => memC P (Complex.exp ((2 * π * (r.2 * y) : ℝ) * I)) Z)
        g.csR Zs := forall₂_csR g Zs (fun sv z => memC P (Complex.exp ((2 * π * (sv * y) : ℝ) * I)) z) hZl hZ
    have hz := forall₂_map_zipWith (R3 := fun (r : ℝ × ℝ × ℝ) (b : Ball × Ball × Ball) =>
        mem P r.1 b.1 ∧ mem P r.2.1 b.2.1 ∧ mem P r.2.2 b.2.2)
      (f := fun (r : ℝ × ℝ) => (-r.1 * Real.cos (2 * π * r.2 * y),
        -((2 * π * r.2) * (-r.1 * Real.sin (2 * π * r.2 * y))), -((2 * π * r.2) * (2 * π * r.2))))
      (f' := fun (r : Ball × Ball × Ball) (Z : CDisc) => (mul P r.1 Z.re, neg (mul P r.2.1 (mul P r.1 Z.im)), r.2.2))
      (fun r b Z hrb hZr => by
        have hre := mem_re hZr
        have him := mem_im hZr
        rw [Complex.exp_ofReal_mul_I_re] at hre
        rw [Complex.exp_ofReal_mul_I_im] at him
        rw [show 2 * π * (r.2 * y) = 2 * π * r.2 * y by ring] at hre him
        exact ⟨mem_mul hrb.1 hre, mem_neg (mem_mul hrb.2.1 (mem_mul hrb.1 him)), hrb.2.2⟩)
      hG.hOM hZs
    have hmH : MemL P ((List.range (n + 1)).map (momR2 (rowsHV g y))) (momH P n G.OM Zs) := memL_momW2 n hz
    have hgH := memL_eser (P := P) (α := -(2 * π * (y * (1 / a)))) (β := -(π * (1 / a)))
      (al := neg (mul P (mulInt 2 (piB P)) (mul P Y G.G.Ai))) (be := neg (mul P (piB P) G.G.Ai))
      (by have := mem_neg (mem_mul (mem_mulInt 2 (mem_piB P)) (mem_mul hY hPG.hAi)); push_cast at this; exact this)
      (mem_neg (mem_mul (mem_piB P) hPG.hAi)) n
    have htH := memL_map_mul hQH (memL_conv (memL_divFact hmH) hgH)
    have hT := memL_addL hEF htH
    rw [List.map_map, zipWith_add_range] at hT
    convert hT using 2
    funext j
    simp only [Function.comp_apply]
    rw [tauSum_inclV, tauSum_inclHV_hz g sp hzc]

theorem jetAllT_ok {n : ℕ} {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ {gs : List GGroup} {pgs : List PG4} {sps : List GSpec} {T : List Ball},
      List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs →
      jetAllT P n ex cz Y pgs sps = some T →
      MemL P ((List.range (n + 1)).map fun j => tauSum (inclAllV gs sps) j y) T
  | [], [], [], T, List.Forall₂.nil, h => by
    simp only [jetAllT, Option.some.injEq] at h
    subst h
    have : (fun j => tauSum (inclAllV [] []) j y) = fun _ => (0 : ℝ) := by funext j; simp [inclAllV, tauSum]
    rw [this]; exact memL_zeroL (n + 1)
  | [], [], _ :: _, T, List.Forall₂.nil, h => by simp [jetAllT] at h
  | _ :: _, _ :: _, [], T, List.Forall₂.cons _ _, h => by simp [jetAllT] at h
  | g :: gs, G :: pgs, sp :: sps, T, List.Forall₂.cons hG hgs, h => by
    simp only [jetAllT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    have h1 := groupJetT_ok hex hcz hG.1 hY hA
    rw [hG.2] at h1
    have h2 := jetAllT_ok hex hcz hY hgs hB
    have := memL_addL h1 h2
    rw [zipWith_add_range] at this
    convert this using 2
    funext j
    simp [inclAllV, tauSum_append]

/-! ## Cosines -/

/-- `d cos(2πby)` as `Re(K exp(B y² + C y + D))` with `B = 0`. -/
noncomputable def quadC (b d : ℝ) : ℂ × ℂ × ℂ × ℂ := ((d : ℂ), 0, ((2 * π * b : ℝ) : ℂ) * I, 0)

theorem ecoef_beta_zero (α : ℂ) : ∀ j : ℕ, ecoef α 0 j = α ^ j / (j.factorial : ℂ) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simp
    | 1 => simp
    | j + 2 =>
      rw [ecoef_succ_succ, ih (j + 1) (by omega)]
      simp only [mul_zero, zero_mul, add_zero]
      rw [Nat.factorial_succ (j + 1)]
      have h1 : ((j + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : (j : ℂ) + 2 ≠ 0 := by norm_cast
      have h3 : (j : ℂ) + 1 + 1 ≠ 0 := by norm_cast
      push_cast
      rw [mul_div_assoc', div_div, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h3 h1)]
      ring

theorem tau_quadC (b d : ℝ) (j : ℕ) (y : ℝ) :
    tauQ (quadC b d) j y = pw2R (d * Real.cos (2 * π * b * y)) (-((2 * π * b) * (d * Real.sin (2 * π * b * y))))
      (-((2 * π * b) * (2 * π * b))) j / (j.factorial : ℝ) := by
  unfold tauQ tau quadC
  simp only [zero_mul, zero_add, mul_zero, add_zero]
  rw [ecoef_beta_zero]
  have e : ((2 * π * b : ℝ) : ℂ) * I * (y : ℂ) = (((2 * π * b * y) : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  have := re_mul_I_pow d (2 * π * b) (2 * π * b * y) j
  have hre : ((d : ℂ) * (Complex.exp ((((2 * π * b * y) : ℝ) : ℂ) * I) *
      ((((2 * π * b : ℝ) : ℂ) * I) ^ j / ((j.factorial : ℕ) : ℂ)))) =
      (((1 / (j.factorial : ℝ)) : ℝ) : ℂ) * ((d : ℂ) * Complex.exp ((((2 * π * b * y) : ℝ) : ℂ) * I) *
        (((2 * π * b : ℝ) : ℂ) * I) ^ j) := by
    push_cast; ring
  rw [hre, Complex.re_ofReal_mul, this]
  ring

/-- The cosine terms of `v` (`q = (βn, βd, dn, dd)`). -/
noncomputable def cosTerms (cos : List (ℕ × ℕ × ℤ × ℕ)) : List (ℂ × ℂ × ℂ × ℂ) :=
  cos.map fun q => quadC ((q.1 : ℝ) / q.2.1) ((q.2.2.1 : ℝ) / q.2.2.2)

theorem memL_cosJet {n : ℕ} {cz : Ball → Option (Ball × Ball)}
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {y : ℝ} {Y : Ball} (hY : mem P y Y) (q : ℕ × ℕ × ℤ × ℕ) (hq1 : 0 < q.2.1) (hq2 : 0 < q.2.2.2) {T : List Ball}
    (h : cosJet P n cz Y q = some T) :
    MemL P ((List.range (n + 1)).map fun j => tauQ (quadC ((q.1 : ℝ) / q.2.1) ((q.2.2.1 : ℝ) / q.2.2.2)) j y) T := by
  unfold cosJet at h
  obtain ⟨⟨C, S⟩, hcs, rfl⟩ := Option.map_eq_some_iff.mp h
  set b : ℝ := (q.1 : ℝ) / q.2.1
  set d : ℝ := (q.2.2.1 : ℝ) / q.2.2.2
  have hB : mem P b (ofRat P q.1 q.2.1) := by
    have := mem_ofRat P (q.1 : ℤ) q.2.1 hq1; simpa [b] using this
  have hD : mem P d (ofRat P q.2.2.1 q.2.2.2) := mem_ofRat P q.2.2.1 q.2.2.2 hq2
  have hw : mem P (2 * π * b) (mul P (mulInt 2 (piB P)) (ofRat P q.1 q.2.1)) := by
    have := mem_mul (mem_mulInt 2 (mem_piB P)) hB; push_cast at this; exact this
  have hc := hcz (mem_mul hB hY) hcs
  rw [show 2 * π * (b * y) = 2 * π * b * y by ring] at hc
  have hx : mem P (d * Real.cos (2 * π * b * y)) (mul P (ofRat P q.2.2.1 q.2.2.2) C) := mem_mul hD hc.1
  have hy : mem P (-((2 * π * b) * (d * Real.sin (2 * π * b * y))))
      (neg (mul P (ofRat P q.2.2.1 q.2.2.2) (mul P (mul P (mulInt 2 (piB P)) (ofRat P q.1 q.2.1)) S))) := by
    have := mem_neg (mem_mul hD (mem_mul hw hc.2))
    rw [show -(d * (2 * π * b * Real.sin (2 * π * b * y))) = -((2 * π * b) * (d * Real.sin (2 * π * b * y))) by ring]
      at this
    exact this
  have hbb : mem P (-((2 * π * b) * (2 * π * b)))
      (neg (mul P (mul P (mulInt 2 (piB P)) (ofRat P q.1 q.2.1)) (mul P (mulInt 2 (piB P)) (ofRat P q.1 q.2.1)))) :=
    mem_neg (mem_mul hw hw)
  have := memL_divFact (memL_pows2 hbb (n + 1) hx hy)
  convert this using 2
  funext j
  rw [tau_quadC]

theorem memL_cosJets {n : ℕ} {cz : Ball → Option (Ball × Ball)}
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ (cos : List (ℕ × ℕ × ℤ × ℕ)), (∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2) → ∀ {T : List Ball},
      cosJets P n cz Y cos = some T → MemL P ((List.range (n + 1)).map fun j => tauSum (cosTerms cos) j y) T
  | [], _, T, h => by
    simp only [cosJets, Option.some.injEq] at h
    subst h
    have : (fun j => tauSum (cosTerms []) j y) = fun _ => (0 : ℝ) := by funext j; simp [cosTerms, tauSum]
    rw [this]; exact memL_zeroL (n + 1)
  | q :: L, hq, T, h => by
    simp only [cosJets, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    have h1 := memL_cosJet hcz hY q (hq q (by simp)).1 (hq q (by simp)).2 hA
    have h2 := memL_cosJets hcz hY L (fun q' hq' => hq q' (by simp [hq'])) hB
    have := memL_addL h1 h2
    rw [zipWith_add_range] at this
    convert this using 2
    funext j
    simp [cosTerms, tauSum, List.map_cons, List.sum_cons, tauQ]

/-! ## Polynomials: Taylor coefficients by synthetic division -/

/-- The `j`-th Taylor coefficient at `y` of the polynomial with coefficients `a` (lowest degree first). -/
noncomputable def Tpoly : List ℝ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, 0, y => c + y * Tpoly cs 0 y
  | _ :: cs, j + 1, y => Tpoly cs j y + y * Tpoly cs (j + 1) y

theorem Tpoly_length : ∀ (a : List ℝ) (j : ℕ) (y : ℝ), a.length ≤ j → Tpoly a j y = 0
  | [], _, _, _ => rfl
  | _ :: cs, 0, _, h => by simp at h
  | _ :: cs, j + 1, y, h => by
    simp only [List.length_cons] at h
    rw [Tpoly, Tpoly_length cs j y (by omega), Tpoly_length cs (j + 1) y (by omega)]; ring

theorem hasDerivAt_Tpoly : ∀ (a : List ℝ) (j : ℕ) (y : ℝ),
    HasDerivAt (Tpoly a j) (((j : ℝ) + 1) * Tpoly a (j + 1) y) y
  | [], j, y => by
    have e : Tpoly [] j = fun _ => 0 := by funext x; rfl
    rw [e]; simpa [Tpoly] using hasDerivAt_const y (0 : ℝ)
  | c :: cs, 0, y => by
    have e : Tpoly (c :: cs) 0 = fun x => c + x * Tpoly cs 0 x := by funext x; rfl
    rw [e]
    have := ((hasDerivAt_id y).mul (hasDerivAt_Tpoly cs 0 y)).const_add c
    refine this.congr_deriv ?_
    simp [Tpoly]
  | c :: cs, j + 1, y => by
    have e : Tpoly (c :: cs) (j + 1) = fun x => Tpoly cs j x + x * Tpoly cs (j + 1) x := by funext x; rfl
    rw [e]
    have := (hasDerivAt_Tpoly cs j y).add ((hasDerivAt_id y).mul (hasDerivAt_Tpoly cs (j + 1) y))
    refine this.congr_deriv ?_
    simp only [Tpoly, id_eq, one_mul]
    push_cast; ring

theorem memL_bshift {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ {a : List ℝ} {A : List Ball}, MemL P a A → MemL P ((List.range A.length).map fun j => Tpoly a j y) (bshift P Y A)
  | [], [], List.Forall₂.nil => by simp [bshift]
  | c :: cs, C :: CS, List.Forall₂.cons hc hcs => by
    have ih := memL_bshift hY hcs
    simp only [bshift, List.length_cons]
    have hlen : (bshift P Y CS).length = CS.length := by
      have := ih.length_eq; simp at this; omega
    have hmap : MemL P (((List.range CS.length).map fun j => Tpoly cs j y).map (y * ·) ++ [0])
        ((bshift P Y CS).map (mul P Y) ++ [⟨0, 0⟩]) :=
      List.rel_append (memL_map_mul hY ih) (List.Forall₂.cons mem_zero_ball List.Forall₂.nil)
    have := memL_addL (List.Forall₂.cons hc ih) hmap
    unfold addL at this
    convert this using 1
    have hcs' : cs.length = CS.length := hcs.length_eq
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
      rcases i with _ | i
      · simp only [List.getElem_cons_zero, Tpoly]
        by_cases h0 : CS.length = 0
        · have hcs0 : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hcs0
          simp [h0, Tpoly]
        · rw [List.getElem_append_left (by simp; omega)]
          simp
      · simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range, Tpoly]
        have hcs : cs.length = CS.length := hcs'
        by_cases hi : i + 1 < CS.length
        · rw [List.getElem_append_left (by simpa using hi)]
          simp
        · have hi' : i + 1 = CS.length := by simp at h1; omega
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_map, List.length_range, List.getElem_singleton]
          rw [Tpoly_length cs (i + 1) y (by omega)]
          ring

theorem memL_padTake {a : List ℝ} {y : ℝ} :
    ∀ (n : ℕ) (k : ℕ) {L : List Ball}, MemL P ((List.range' k L.length).map fun j => Tpoly a j y) L →
      a.length ≤ k + L.length → MemL P ((List.range' k n).map fun j => Tpoly a j y) (padTake n L)
  | 0, _, _, _, _ => by simp [padTake]
  | n + 1, k, [], _, hlen => by
    simp only [padTake, List.range'_succ, List.map_cons]
    refine List.Forall₂.cons ?_ (memL_padTake n (k + 1) (by simp) (by simp at hlen ⊢; omega))
    rw [Tpoly_length a k y (by simpa using hlen)]
    exact mem_zero_ball
  | n + 1, k, B :: L, h, hlen => by
    simp only [List.length_cons, List.range'_succ, List.map_cons] at h
    cases h with
    | cons hb hL =>
      simp only [padTake, List.range'_succ, List.map_cons]
      exact List.Forall₂.cons hb (memL_padTake n (k + 1) hL (by simp at hlen ⊢; omega))

/-! ## `v` and `φ` -/

/-- `ψ` as the real polynomial `[q₀, 0, q₁, 0, …]`. -/
noncomputable def psiR : List (ℤ × ℕ) → List ℝ
  | [] => []
  | q :: L => (q.1 : ℝ) / q.2 :: 0 :: psiR L

theorem memL_psiPoly : ∀ (psi : List (ℤ × ℕ)), (∀ q ∈ psi, 0 < q.2) → MemL P (psiR psi) (psiPoly P psi)
  | [], _ => List.Forall₂.nil
  | q :: L, h => List.Forall₂.cons (mem_ofRat P q.1 q.2 (h q (by simp)))
      (List.Forall₂.cons mem_zero_ball (memL_psiPoly L (fun q' hq' => h q' (by simp [hq']))))

theorem psiR_length (psi : List (ℤ × ℕ)) : (psiR psi).length = 2 * psi.length := by
  induction psi with
  | nil => rfl
  | cons q L ih => simp [psiR, ih]; ring

theorem psiPoly_length (psi : List (ℤ × ℕ)) : (psiPoly P psi).length = 2 * psi.length := by
  induction psi with
  | nil => rfl
  | cons q L ih => simp [psiPoly, ih]; ring

/-- The terms of `v`: signed Gaussian pairs of the groups (included ones) and the cosines. -/
noncomputable def vTerms (gs : List GGroup) (sps : List GSpec) (cos : List (ℕ × ℕ × ℤ × ℕ)) :
    List (ℂ × ℂ × ℂ × ℂ) := inclAllV gs sps ++ cosTerms cos

/-- The normalized Taylor coefficients of `1 - v + ψ` (included Gaussian terms). -/
noncomputable def Tphi (gs : List GGroup) (sps : List GSpec) (cos : List (ℕ × ℕ × ℤ × ℕ)) (psi : List (ℤ × ℕ))
    (j : ℕ) (y : ℝ) : ℝ :=
  (if j = 0 then 1 else 0) + Tpoly (psiR psi) j y - tauSum (vTerms gs sps cos) j y

theorem hasDerivAt_Tphi (gs : List GGroup) (sps : List GSpec) (cos : List (ℕ × ℕ × ℤ × ℕ)) (psi : List (ℤ × ℕ))
    (j : ℕ) (y : ℝ) :
    HasDerivAt (Tphi gs sps cos psi j) (((j : ℝ) + 1) * Tphi gs sps cos psi (j + 1) y) y := by
  have h := ((hasDerivAt_const y (if j = 0 then (1 : ℝ) else 0)).add (hasDerivAt_Tpoly (psiR psi) j y)).sub
    (hasDerivAt_tauSum (vTerms gs sps cos) j y)
  unfold Tphi
  refine h.congr_deriv ?_
  simp only [Nat.add_one_ne_zero, if_false, zero_add]
  ring

theorem memL_subL {xs ys : List ℝ} {as bs : List Ball} (h1 : MemL P xs as) (h2 : MemL P ys bs) :
    MemL P (List.zipWith (· - ·) xs ys) (List.zipWith sub as bs) := by
  induction h1 generalizing ys bs with
  | nil => simp
  | cons hx _ ih =>
    cases h2 with
    | nil => simp
    | cons hy h2' => exact List.Forall₂.cons (mem_sub hx hy) (ih h2')

theorem zipWith_sub_range (f g : ℕ → ℝ) (n : ℕ) :
    List.zipWith (· - ·) ((List.range n).map f) ((List.range n).map g) = (List.range n).map fun i => f i - g i := by
  rw [List.zipWith_map]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.zipWith_append (by simp), ih]
    simp

theorem memL_vJet {n : ℕ} {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {y : ℝ} {Y : Ball} (hY : mem P y Y) {gs : List GGroup} {pgs : List PG4} {sps : List GSpec}
    (hgs : List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs)
    {cos : List (ℕ × ℕ × ℤ × ℕ)} (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2) {T : List Ball}
    (h : vJet P n ex cz pgs sps cos Y = some T) :
    MemL P ((List.range (n + 1)).map fun j => tauSum (vTerms gs sps cos) j y) T := by
  unfold vJet at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨A, hA, B, hB, rfl⟩ := h
  have := memL_addL (jetAllT_ok hex hcz hY hgs hA) (memL_cosJets hcz hY cos hcos hB)
  rw [zipWith_add_range] at this
  convert this using 2
  funext j
  rw [vTerms, tauSum_append]

theorem memL_phiJet {n : ℕ} {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {y : ℝ} {Y : Ball} (hY : mem P y Y) {gs : List GGroup} {pgs : List PG4} {sps : List GSpec}
    (hgs : List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs)
    {cos : List (ℕ × ℕ × ℤ × ℕ)} (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2)
    {psi : List (ℤ × ℕ)} (hpsi : ∀ q ∈ psi, 0 < q.2) {T : List Ball}
    (h : phiJet P n ex cz pgs sps cos (psiPoly P psi) Y = some T) :
    MemL P ((List.range (n + 1)).map fun j => Tphi gs sps cos psi j y) T := by
  unfold phiJet at h
  obtain ⟨V, hV, rfl⟩ := Option.map_eq_some_iff.mp h
  have hv := memL_vJet hex hcz hY hgs hcos hV
  have hb := memL_bshift hY (memL_psiPoly (P := P) psi hpsi)
  have hlenb : (bshift P Y (psiPoly P psi)).length = (psiPoly P psi).length := by
    have := hb.length_eq; simp at this; omega
  have hpad := memL_padTake (a := psiR psi) (y := y) (n + 1) 0 (L := bshift P Y (psiPoly P psi))
    (by rw [hlenb, ← List.range_eq_range']; exact hb)
    (by rw [hlenb, psiR_length, psiPoly_length]; omega)
  rw [← List.range_eq_range'] at hpad
  have h1 : MemL P ((List.range (n + 1)).map fun j => if j = 0 then (1 : ℝ) else 0) (ofInt P 1 :: zeroL n) := by
    rw [List.range_succ_eq_map, List.map_cons]
    refine List.Forall₂.cons (by simpa using mem_ofInt P 1) ?_
    have := memL_zeroL (P := P) n
    simpa [List.map_map, Function.comp_def] using this
  have h2 := memL_addL h1 hpad
  rw [zipWith_add_range] at h2
  have h3 := memL_subL h2 hv
  rw [zipWith_sub_range] at h3
  unfold addL at h3
  exact h3

end SignUnc.Chk
