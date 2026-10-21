import SignUnc.APos

/-!
# Lemma 3.2: the identity `g(0) = ∫_O g W + Σ d_k g(β_k) + ∫_I g ρ`

For an even real integrable self-dual `g` (`ĝ = g`) and a certificate (Gaussian pairs, cosines with `β_k ≥ r`,
an even continuous `ψ`).  Ingredients: the multiplication formula `∫ 𝓕f · g = ∫ f · 𝓕g`, the Fourier transform of an
even real function is its cosine transform, `g(β) = ∫ g(x) cos(2πβx) dx`.
-/

open MeasureTheory Real Complex Set Filter
open scoped FourierTransform

namespace SignUnc

/-- The multiplication formula on `ℝ`. -/
theorem integral_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner hf hg
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext x y; simp [real_inner_comm]
  rw [hflip] at h
  simp only [smul_eq_mul] at h
  exact h

/-- The multiplication formula for real functions, with `ft`. -/
theorem integral_ft_mul {φ g : ℝ → ℝ} (hφ : Integrable φ) (hg : Integrable g) :
    ∫ ξ, ft φ ξ * ((g ξ : ℝ) : ℂ) = ∫ x, ((φ x : ℝ) : ℂ) * ft g x :=
  integral_fourier_mul hφ.ofReal hg.ofReal

/-- The cosine transform `∫ φ(t) cos(2πyt) dt`. -/
noncomputable def cosT (φ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t, φ t * Real.cos (2 * π * y * t)

theorem integrable_mul_cos {φ : ℝ → ℝ} (hφ : Integrable φ) (y : ℝ) :
    Integrable (fun t => φ t * Real.cos (2 * π * y * t)) :=
  hφ.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun t => by simpa using Real.abs_cos_le_one _)

theorem integrable_mul_sin {φ : ℝ → ℝ} (hφ : Integrable φ) (y : ℝ) :
    Integrable (fun t => φ t * Real.sin (2 * π * y * t)) :=
  hφ.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun t => by simpa using Real.abs_sin_le_one _)

/-- The Fourier transform of an even real integrable function is its cosine transform. -/
theorem ft_even {φ : ℝ → ℝ} (hφ : Integrable φ) (he : ∀ x, φ (-x) = φ x) (y : ℝ) :
    ft φ y = ((cosT φ y : ℝ) : ℂ) := by
  unfold ft cosT
  rw [fourier_real_eq_integral_exp_smul]
  have h1 : ∀ t : ℝ, cexp (((-2 * π * t * y : ℝ) : ℂ) * I) • ((φ t : ℝ) : ℂ) =
      ((φ t * Real.cos (2 * π * y * t) : ℝ) : ℂ) - I * ((φ t * Real.sin (2 * π * y * t) : ℝ) : ℂ) := by
    intro t
    rw [smul_eq_mul, Complex.exp_mul_I]
    have e1 : ((-2 * π * t * y : ℝ) : ℂ) = -((2 * π * y * t : ℝ) : ℂ) := by push_cast; ring
    rw [e1, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  simp_rw [h1]
  rw [integral_sub, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  rotate_left
  · exact (integrable_mul_cos hφ y).ofReal
  · exact ((integrable_mul_sin hφ y).ofReal.const_mul I)
  have hodd : ∫ t, φ t * Real.sin (2 * π * y * t) = 0 := by
    have h2 := integral_neg_eq_self (fun t => φ t * Real.sin (2 * π * y * t)) volume
    have h3 : (fun t => φ (-t) * Real.sin (2 * π * y * -t)) = fun t => -(φ t * Real.sin (2 * π * y * t)) := by
      funext t; rw [he, show 2 * π * y * -t = -(2 * π * y * t) by ring, Real.sin_neg]; ring
    rw [show (∫ t, φ (-t) * Real.sin (2 * π * y * -t)) = ∫ t, -(φ t * Real.sin (2 * π * y * t)) by rw [h3],
      integral_neg] at h2
    linarith
  rw [hodd]; simp

/-- For self-dual even real `g`: `g(β) = ∫ g(x) cos(2πβx) dx`. -/
theorem eval_eq_cosT {g : ℝ → ℝ} (hi : Integrable g) (he : ∀ x, g (-x) = g x)
    (hft : ft g = fun x => (g x : ℂ)) (β : ℝ) : g β = cosT g β := by
  have := ft_even hi he β
  rw [hft] at this
  simp only at this
  exact_mod_cast this

/-- `∫ (𝓕 ↑φ) · ↑g = ∫ ↑φ · ↑g` for self-dual `g`, in real form: `∫ ψ g = ∫ φ g` when `ft φ = ψ`. -/
theorem integral_pair_selfdual {g φ ψ : ℝ → ℝ} (hg : Integrable g) (hft : ft g = fun x => (g x : ℂ))
    (hφ : Integrable φ) (hψ : ft φ = fun x => (ψ x : ℂ)) : ∫ x, ψ x * g x = ∫ x, φ x * g x := by
  have h := integral_ft_mul hφ hg
  rw [hψ, hft] at h
  have h' : ((∫ x, ψ x * g x : ℝ) : ℂ) = ((∫ x, φ x * g x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    simpa using h
  exact_mod_cast h'

/-! ## Certificates (Definition 3.1) -/

/-- A lower-bound certificate: pairs `(a, s, c)`, cosines `(β, d)`, an even function `ψ`, for the radius `r`. -/
structure LCert where
  r : ℝ
  pairs : List (ℝ × ℝ × ℝ)
  coss : List (ℝ × ℝ)
  psi : ℝ → ℝ

namespace LCert

variable (C : LCert)

/-- The Gaussian part `Σ c (b - b̂)` of `v`. -/
noncomputable def vG (x : ℝ) : ℝ := (C.pairs.map fun p => p.2.2 * (gb p.1 p.2.1 x - gbh p.1 p.2.1 x)).sum

/-- The cosine part `Σ d cos(2πβx)` of `v`. -/
noncomputable def vC (x : ℝ) : ℝ := (C.coss.map fun q => q.2 * Real.cos (2 * π * q.1 * x)).sum

noncomputable def v (x : ℝ) : ℝ := C.vG x + C.vC x

/-- `φ = (1 - v + ψ) 1_I`. -/
noncomputable def phi (x : ℝ) : ℝ := (Icc (-C.r) C.r).indicator (fun x => 1 - C.v x + C.psi x) x

noncomputable def phihat (y : ℝ) : ℝ := cosT C.phi y

noncomputable def W (y : ℝ) : ℝ := 1 - C.v y + C.phihat y

noncomputable def rho (x : ℝ) : ℝ := C.phihat x - C.psi x

/-- Hypotheses on the data: positive widths, `β_k ≥ r`, `d_k ≥ 0`, `ψ` even and continuous. -/
structure Ok : Prop where
  hr : 0 < C.r
  ha : ∀ p ∈ C.pairs, 0 < p.1
  hβ : ∀ q ∈ C.coss, C.r ≤ q.1 ∧ 0 ≤ q.2
  hψc : Continuous C.psi
  hψe : ∀ x, C.psi (-x) = C.psi x

variable {C}

theorem continuous_vG : Continuous C.vG := by
  unfold vG
  induction C.pairs with
  | nil => simpa using continuous_const
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((continuous_gb _ _).sub (continuous_gbh _ _)).const_smul p.2.2 |>.add ih

theorem continuous_vC : Continuous C.vC := by
  unfold vC
  induction C.coss with
  | nil => simpa using continuous_const
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuous_const.mul (by fun_prop)).add ih

theorem continuous_v : Continuous C.v := continuous_vG.add continuous_vC

theorem v_neg (x : ℝ) : C.v (-x) = C.v x := by
  unfold v vG vC
  congr 1
  · congr 1; refine List.map_congr_left (fun p _ => ?_); rw [gb_neg, gbh_neg]
  · congr 1; refine List.map_congr_left (fun q _ => ?_); rw [show 2 * π * q.1 * -x = -(2 * π * q.1 * x) by ring,
      Real.cos_neg]

theorem abs_gb_le {a : ℝ} (ha : 0 < a) (s x : ℝ) : |gb a s x| ≤ 2 := by
  unfold gb
  have h1 : Real.exp (-π * a * (x - s) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have h0 : 0 ≤ π * a * (x - s) ^ 2 := by have := Real.pi_pos; positivity
    linarith)
  have h2 : Real.exp (-π * a * (x + s) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have h0 : 0 ≤ π * a * (x + s) ^ 2 := by have := Real.pi_pos; positivity
    linarith)
  rw [abs_of_nonneg (by positivity)]; linarith

theorem abs_gbh_le {a : ℝ} (ha : 0 < a) (s y : ℝ) : |gbh a s y| ≤ 2 / Real.sqrt a := by
  unfold gbh
  have h1 : Real.exp (-π * y ^ 2 / a) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := Real.pi_pos; have : 0 ≤ y ^ 2 := sq_nonneg _
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le)
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.sqrt a), abs_of_pos (Real.exp_pos _)]
  have := Real.abs_cos_le_one (2 * π * s * y)
  have hq : 0 < 2 / Real.sqrt a := by positivity
  calc 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * |Real.cos (2 * π * s * y)| ≤ 2 / Real.sqrt a * 1 * 1 := by
        gcongr
    _ = 2 / Real.sqrt a := by ring

/-- `v` is bounded. -/
theorem bdd_v (h : C.Ok) : ∃ B, ∀ x, |C.v x| ≤ B := by
  refine ⟨(C.pairs.map fun p => |p.2.2| * (2 + 2 / Real.sqrt p.1)).sum + (C.coss.map fun q => |q.2|).sum, fun x => ?_⟩
  unfold v vG vC
  have hG : ∀ L : List (ℝ × ℝ × ℝ), (∀ p ∈ L, 0 < p.1) →
      |(L.map fun p => p.2.2 * (gb p.1 p.2.1 x - gbh p.1 p.2.1 x)).sum| ≤
        (L.map fun p => |p.2.2| * (2 + 2 / Real.sqrt p.1)).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons p L ih =>
      simp only [List.map_cons, List.sum_cons]
      have hp := hL p (by simp)
      have h1 : |p.2.2 * (gb p.1 p.2.1 x - gbh p.1 p.2.1 x)| ≤ |p.2.2| * (2 + 2 / Real.sqrt p.1) := by
        rw [abs_mul]
        gcongr
        exact (abs_sub _ _).trans (add_le_add (abs_gb_le hp _ _) (abs_gbh_le hp _ _))
      exact (abs_add_le _ _).trans (add_le_add h1 (ih (fun q hq => hL q (by simp [hq]))))
  have hC : ∀ L : List (ℝ × ℝ), |(L.map fun q => q.2 * Real.cos (2 * π * q.1 * x)).sum| ≤ (L.map fun q => |q.2|).sum := by
    intro L
    induction L with
    | nil => simp
    | cons q L ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 : |q.2 * Real.cos (2 * π * q.1 * x)| ≤ |q.2| := by
        rw [abs_mul]; have := Real.abs_cos_le_one (2 * π * q.1 * x)
        calc |q.2| * |Real.cos (2 * π * q.1 * x)| ≤ |q.2| * 1 := by gcongr
          _ = |q.2| := mul_one _
      exact (abs_add_le _ _).trans (add_le_add h1 ih)
  exact (abs_add_le _ _).trans (add_le_add (hG C.pairs h.ha) (hC C.coss))

theorem phi_neg (h : C.Ok) (x : ℝ) : C.phi (-x) = C.phi x := by
  unfold phi
  by_cases hx : x ∈ Icc (-C.r) C.r
  · have hx' : -x ∈ Icc (-C.r) C.r := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [indicator_of_mem hx', indicator_of_mem hx, v_neg, h.hψe]
  · have hx' : -x ∉ Icc (-C.r) C.r := fun h' => hx ⟨by linarith [h'.2], by linarith [h'.1]⟩
    rw [indicator_of_notMem hx', indicator_of_notMem hx]

theorem integrable_phi (h : C.Ok) : Integrable C.phi := by
  unfold phi
  rw [integrable_indicator_iff measurableSet_Icc]
  exact ((continuous_const.sub continuous_v).add h.hψc).continuousOn.integrableOn_Icc

theorem ft_phi (h : C.Ok) : ft C.phi = fun y => ((C.phihat y : ℝ) : ℂ) := by
  funext y; exact ft_even (integrable_phi h) (phi_neg h) y

theorem continuous_phihat (h : C.Ok) : Continuous C.phihat := by
  have hc := Complex.continuous_re.comp (continuous_ft (integrable_phi h))
  rw [ft_phi h] at hc
  simpa [Function.comp_def] using hc

theorem abs_phihat_le (h : C.Ok) (y : ℝ) : |C.phihat y| ≤ ∫ t, |C.phi t| := by
  unfold phihat cosT
  refine (abs_integral_le_integral_abs).trans (integral_mono (integrable_mul_cos (integrable_phi h) y).abs
    (integrable_phi h).abs (fun t => ?_))
  simp only [abs_mul]
  have := Real.abs_cos_le_one (2 * π * y * t)
  calc |C.phi t| * |Real.cos (2 * π * y * t)| ≤ |C.phi t| * 1 := by gcongr
    _ = |C.phi t| := mul_one _

theorem phi_bdd (h : C.Ok) : ∃ B, ∀ x, |C.phi x| ≤ B := by
  obtain ⟨Bv, hBv⟩ := bdd_v h
  obtain ⟨Bp, hBp⟩ := (isCompact_Icc (a := -C.r) (b := C.r)).exists_bound_of_continuousOn h.hψc.continuousOn
  refine ⟨1 + Bv + Bp, fun x => ?_⟩
  unfold phi
  by_cases hx : x ∈ Icc (-C.r) C.r
  · rw [indicator_of_mem hx]
    have := hBp x hx; rw [Real.norm_eq_abs] at this
    calc |1 - C.v x + C.psi x| ≤ |1 - C.v x| + |C.psi x| := abs_add_le _ _
      _ ≤ (1 + |C.v x|) + |C.psi x| := by gcongr; exact (abs_sub _ _).trans (by simp)
      _ ≤ 1 + Bv + Bp := by linarith [hBv x]
  · rw [indicator_of_notMem hx, abs_zero]
    have := hBv 0; have := abs_nonneg (C.v 0)
    have : 0 ≤ Bp := le_trans (norm_nonneg _) (hBp 0 ⟨by linarith [h.hr], h.hr.le⟩)
    linarith

end LCert

theorem integrable_mul_listSum {g : ℝ → ℝ} {ι : Type*} (L : List ι) (f : ι → ℝ → ℝ)
    (hint : ∀ i ∈ L, Integrable (fun x => g x * f i x)) : Integrable (fun x => g x * (L.map fun i => f i x).sum) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact (hint i (by simp)).add (ih (fun j hj => hint j (by simp [hj])))

theorem integral_mul_listSum {g : ℝ → ℝ} {ι : Type*} (L : List ι) (f : ι → ℝ → ℝ)
    (hint : ∀ i ∈ L, Integrable (fun x => g x * f i x)) :
    ∫ x, g x * (L.map fun i => f i x).sum = (L.map fun i => ∫ x, g x * f i x).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    rw [integral_add (hint i (by simp)) (integrable_mul_listSum L f (fun j hj => hint j (by simp [hj]))),
      ih (fun j hj => hint j (by simp [hj]))]

namespace LCert

variable {C : LCert}

/-- Lemma 3.2 of the paper. -/
theorem identity (h : C.Ok) {g : ℝ → ℝ} (hi : Integrable g) (he : ∀ x, g (-x) = g x)
    (hft : ft g = fun x => (g x : ℂ)) :
    g 0 = (∫ y in {y | C.r < |y|}, g y * C.W y) + (C.coss.map fun q => q.2 * g q.1).sum +
      ∫ x in Icc (-C.r) C.r, g x * C.rho x := by
  have hg0 : g 0 = ∫ x, g x := by
    have := ft_zero_re g; rw [hft] at this; simpa using this
  obtain ⟨Bv, hBv⟩ := bdd_v h
  obtain ⟨Bφ, hBφ⟩ := phi_bdd h
  have hgv : Integrable (fun x => g x * C.v x) :=
    hi.mul_bdd continuous_v.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hBv x)
  have hgφ : Integrable (fun x => g x * C.phi x) :=
    hi.mul_bdd (integrable_phi h).aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hBφ x)
  have hgφh : Integrable (fun x => g x * C.phihat x) :=
    hi.mul_bdd (continuous_phihat h).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using abs_phihat_le h x)
  -- `∫ g φ̂ = ∫ g φ`
  have h1 : ∫ x, g x * C.phihat x = ∫ x, g x * C.phi x := by
    have := integral_pair_selfdual hi hft (integrable_phi h) (ft_phi h)
    simpa [mul_comm] using this
  -- `∫ g v = Σ d g(β)`
  have hpair : ∀ p ∈ C.pairs, Integrable (fun x => g x * (p.2.2 * (gb p.1 p.2.1 x - gbh p.1 p.2.1 x))) := by
    intro p hp
    have ha := h.ha p hp
    refine hi.mul_bdd (c := |p.2.2| * (2 + 2 / Real.sqrt p.1))
      (continuous_const.mul ((continuous_gb _ _).sub (continuous_gbh _ _))).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    gcongr
    exact (abs_sub _ _).trans (add_le_add (abs_gb_le ha _ _) (abs_gbh_le ha _ _))
  have hcos : ∀ q ∈ C.coss, Integrable (fun x => g x * (q.2 * Real.cos (2 * π * q.1 * x))) := by
    intro q _
    refine hi.mul_bdd (c := |q.2|) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := Real.abs_cos_le_one (2 * π * q.1 * x)
    calc |q.2| * |Real.cos (2 * π * q.1 * x)| ≤ |q.2| * 1 := by gcongr
      _ = |q.2| := mul_one _
  have hG0 : ∫ x, g x * C.vG x = 0 := by
    unfold vG
    rw [integral_mul_listSum C.pairs (fun p x => p.2.2 * (gb p.1 p.2.1 x - gbh p.1 p.2.1 x)) hpair]
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    have ha := h.ha p hp
    have hgb : Integrable (fun x => g x * gb p.1 p.2.1 x) :=
      hi.mul_bdd (c := 2) (continuous_gb _ _).aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using abs_gb_le ha p.2.1 x)
    have hgbh : Integrable (fun x => g x * gbh p.1 p.2.1 x) :=
      hi.mul_bdd (c := 2 / Real.sqrt p.1) (continuous_gbh _ _).aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using abs_gbh_le ha p.2.1 x)
    have hsd := integral_pair_selfdual hi hft (integrable_gb ha p.2.1) (ft_gb ha p.2.1)
    simp only [mul_sub, mul_left_comm (g _)]
    rw [integral_sub (hgb.const_mul p.2.2) (hgbh.const_mul p.2.2), integral_const_mul, integral_const_mul]
    have e1 : ∫ x, g x * gb p.1 p.2.1 x = ∫ x, gb p.1 p.2.1 x * g x := by simp only [mul_comm]
    have e2 : ∫ x, g x * gbh p.1 p.2.1 x = ∫ x, gbh p.1 p.2.1 x * g x := by simp only [mul_comm]
    rw [e1, e2, hsd]; ring
  have hC : ∫ x, g x * C.vC x = (C.coss.map fun q => q.2 * g q.1).sum := by
    unfold vC
    rw [integral_mul_listSum C.coss (fun q x => q.2 * Real.cos (2 * π * q.1 * x)) hcos]
    congr 1
    refine List.map_congr_left (fun q _ => ?_)
    simp only [mul_left_comm (g _)]
    rw [integral_const_mul, eval_eq_cosT hi he hft q.1]
    rfl
  have hgvG : Integrable (fun x => g x * C.vG x) := integrable_mul_listSum C.pairs _ hpair
  have hgvC : Integrable (fun x => g x * C.vC x) := integrable_mul_listSum C.coss _ hcos
  have h2 : ∫ x, g x * C.v x = (C.coss.map fun q => q.2 * g q.1).sum := by
    unfold v
    simp only [mul_add]
    rw [integral_add hgvG hgvC, hG0, hC, zero_add]
  -- assemble
  set F : ℝ → ℝ := fun x => g x * (1 - C.v x - C.phi x + C.phihat x) with hFdef
  have hFeq : F = fun x => g x - g x * C.v x - g x * C.phi x + g x * C.phihat x := by
    funext x; simp only [hFdef]; ring
  have hF : Integrable F := by rw [hFeq]; exact ((hi.sub hgv).sub hgφ).add hgφh
  have hFint : ∫ x, F x = g 0 - (C.coss.map fun q => q.2 * g q.1).sum := by
    have e : ∫ x, F x = ∫ x, (g x - g x * C.v x - g x * C.phi x + g x * C.phihat x) := by rw [hFeq]
    rw [e, integral_add, integral_sub, integral_sub, h1, h2, ← hg0]
    · ring
    · exact hi
    · exact hgv
    · exact hi.sub hgv
    · exact hgφ
    · exact (hi.sub hgv).sub hgφ
    · exact hgφh
  have hsplit := integral_add_compl (measurableSet_Icc (a := -C.r) (b := C.r)) hF
  have hcompl : (Icc (-C.r) C.r)ᶜ = {y | C.r < |y|} := by
    ext y; simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, not_and_or, not_le]
    constructor
    · rintro (hy | hy)
      · rw [abs_of_neg (by linarith [h.hr])]; linarith
      · rw [abs_of_pos (by linarith [h.hr])]; exact hy
    · intro hy
      rcases le_or_gt 0 y with hy0 | hy0
      · right; rwa [abs_of_nonneg hy0] at hy
      · left; rw [abs_of_neg hy0] at hy; linarith
  have hI : ∫ x in Icc (-C.r) C.r, F x = ∫ x in Icc (-C.r) C.r, g x * C.rho x := by
    refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    simp only [hFdef, rho, phi, indicator_of_mem hx]
    ring
  have hO : ∫ x in (Icc (-C.r) C.r)ᶜ, F x = ∫ y in {y | C.r < |y|}, g y * C.W y := by
    rw [hcompl]
    refine setIntegral_congr_fun (measurableSet_lt measurable_const (continuous_abs.measurable)) (fun y hy => ?_)
    have hy' : y ∉ Icc (-C.r) C.r := by rw [← mem_compl_iff, hcompl]; exact hy
    simp only [hFdef, W, phi, indicator_of_notMem hy']
    ring
  rw [hI, hO, hFint] at hsplit
  linarith

end LCert

end SignUnc
