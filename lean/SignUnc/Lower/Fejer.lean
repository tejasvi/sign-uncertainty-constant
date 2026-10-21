import SignUnc.APos
import SignUnc.Lower.Identity

/-!
# Lemma 2.4 of the paper, first part: `C_{6.11} ≥ A₊(1)²`

* `tendsto_gauss_fejer`: for `F ∈ L¹` continuous at `0`, `∫ 𝓕F(ξ) e^{-ξ²/c} dξ → F(0)` as `c → ∞` (a Gaussian
  version of the Fejér argument, from Mathlib's Gaussian approximate identity);
* `integrable_fourier_of_nonneg_tail`: if moreover `𝓕F` is real and `≥ 0` for `|ξ| ≥ R`, then `𝓕F ∈ L¹`.
-/

open MeasureTheory Real Complex Set Filter
open scoped FourierTransform ENNReal Topology Convolution

namespace SignUnc

/-- Gaussian Fejér: `∫ 𝓕F(ξ) e^{-ξ²/c} dξ → F(0)` as `c → ∞`. -/
theorem tendsto_gauss_fejer {F : ℝ → ℂ} (hF : Integrable F) (h0 : ContinuousAt F 0) :
    Tendsto (fun c : ℝ => ∫ ξ : ℝ, 𝓕 F ξ * cexp (-((c⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2)) atTop (𝓝 (F 0)) := by
  have h := Real.tendsto_integral_gaussian_smul' hF h0
  refine h.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  have hb : 0 < ((c⁻¹ : ℝ) : ℂ).re := by simp [hc]
  have hG : Integrable (fun ξ : ℝ => cexp (-((c⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2)) := integrable_cexp_neg_mul_sq hb
  rw [integral_fourier_mul hF hG]
  congr 1
  ext x
  have hft := fourier_gaussian_innerProductSpace (V := ℝ) hb x
  have hfun : (fun ξ : ℝ => cexp (-((c⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2)) =
      (fun v : ℝ => cexp (-((c⁻¹ : ℝ) : ℂ) * ((‖v‖ : ℝ) : ℂ) ^ 2)) := by
    funext v; congr 2; rw [Real.norm_eq_abs]; norm_cast; rw [sq_abs]
  rw [hfun, hft]
  simp only [Module.finrank_self, Nat.cast_one, smul_eq_mul, zero_sub, norm_neg, Real.norm_eq_abs]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [show (π : ℂ) / ((c⁻¹ : ℝ) : ℂ) = (π : ℂ) * c by push_cast; field_simp]
  rw [show -(π : ℂ) ^ 2 * ((|x| : ℝ) : ℂ) ^ 2 / ((c⁻¹ : ℝ) : ℂ) = -(π : ℂ) ^ 2 * c * ((|x| : ℝ) : ℂ) ^ 2 by
    push_cast; field_simp]
  ring

theorem norm_fourier_le {F : ℝ → ℂ} (ξ : ℝ) : ‖𝓕 F ξ‖ ≤ ∫ x, ‖F x‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext x
  rw [Circle.norm_smul]

theorem continuous_fourier {F : ℝ → ℂ} (hF : Integrable F) : Continuous (𝓕 F) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hF

/-- Lemma 2.4, first part: `𝓕F ∈ L¹` when `F ∈ L¹` is continuous at `0` and `𝓕F` is real and `≥ 0` for `|ξ| ≥ R`. -/
theorem integrable_fourier_of_nonneg_tail {F : ℝ → ℂ} (hF : Integrable F) (h0 : ContinuousAt F 0) {R : ℝ}
    (hR : ∀ ξ : ℝ, R ≤ |ξ| → (𝓕 F ξ).im = 0 ∧ 0 ≤ (𝓕 F ξ).re) : Integrable (𝓕 F) := by
  set u := 𝓕 F with hu_def
  have hu : Continuous u := continuous_fourier hF
  set S : Set ℝ := {ξ | R ≤ |ξ|} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  set B := ∫ x, ‖F x‖
  have hub : ∀ ξ, ‖u ξ‖ ≤ B := fun ξ => norm_fourier_le ξ
  -- the Gaussian weights w n ξ = e^{-ξ²/(n+1)}
  set w : ℕ → ℝ → ℝ := fun n ξ => Real.exp (-((n : ℝ) + 1)⁻¹ * ξ ^ 2) with hw
  have hw01 : ∀ n ξ, 0 < w n ξ ∧ w n ξ ≤ 1 := fun n ξ => ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by
    have : 0 ≤ ((n : ℝ) + 1)⁻¹ * ξ ^ 2 := by positivity
    linarith)⟩
  have hwint : ∀ n, Integrable (w n) := fun n => by
    have := integrable_exp_neg_mul_sq (b := ((n : ℝ) + 1)⁻¹) (by positivity)
    simpa [hw, neg_mul] using this
  -- the integrals T n → F 0
  set T : ℕ → ℂ := fun n => ∫ ξ : ℝ, u ξ * cexp (-((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2) with hT
  have hTlim : Tendsto T atTop (𝓝 (F 0)) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_gauss_fejer hF h0).comp h1
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖T n‖ ≤ C := by
    obtain ⟨C, hC⟩ := hTlim.norm.bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  -- real parts
  set g : ℕ → ℝ → ℝ := fun n ξ => (u ξ).re * w n ξ with hg
  have hgint : ∀ n, Integrable (g n) := fun n => by
    refine (hwint n).bdd_mul (c := B) (Complex.continuous_re.comp hu).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hub ξ)
  have hTre : ∀ n, (T n).re = ∫ ξ, g n ξ := by
    intro n
    have hint : Integrable (fun ξ : ℝ => u ξ * cexp (-((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2)) := by
      have hG := integrable_cexp_neg_mul_sq (b := ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; positivity)
      refine hG.bdd_mul (c := B) hu.aestronglyMeasurable (Eventually.of_forall fun ξ => hub ξ)
    calc (T n).re = ∫ ξ, (u ξ * cexp (-((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2)).re := (integral_re hint).symm
      _ = ∫ ξ, g n ξ := by
          congr 1; ext ξ
          have e : -((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2 = ((-((n : ℝ) + 1)⁻¹ * ξ ^ 2 : ℝ) : ℂ) := by
            push_cast; ring
          rw [e, ← Complex.ofReal_exp, Complex.re_mul_ofReal]
  -- the part on the complement of S is bounded by the integral of ‖u‖ over [-R, R]
  have hcomp : IntegrableOn (fun ξ => ‖u ξ‖) Sᶜ := by
    have hsub : Sᶜ ⊆ Icc (-R) R := by
      intro ξ hξ
      simp only [hS, mem_compl_iff, mem_ofPred_eq, not_le] at hξ
      exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩
    exact (hu.norm.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  set B0 := ∫ ξ in Sᶜ, ‖u ξ‖
  have hSbound : ∀ n, ∫ ξ in S, g n ξ ≤ C + B0 := by
    intro n
    have hsplit := integral_add_compl hSm (hgint n)
    have h1 : |∫ ξ, g n ξ| ≤ C := by
      rw [← hTre]; exact (Complex.abs_re_le_norm _).trans (hC n)
    have h2 : -B0 ≤ ∫ ξ in Sᶜ, g n ξ := by
      have : |∫ ξ in Sᶜ, g n ξ| ≤ B0 := by
        refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on (hgint n).integrableOn.abs hcomp
          hSm.compl (fun ξ _ => ?_))
        simp only [hg, abs_mul, abs_of_pos (hw01 n ξ).1]
        calc |(u ξ).re| * w n ξ ≤ |(u ξ).re| * 1 := by gcongr; exact (hw01 n ξ).2
          _ ≤ ‖u ξ‖ := by rw [mul_one]; exact Complex.abs_re_le_norm _
      linarith [neg_abs_le (∫ ξ in Sᶜ, g n ξ)]
    linarith [le_abs_self (∫ ξ, g n ξ)]
  -- monotone convergence on S
  have hlin : ∫⁻ ξ in S, ENNReal.ofReal (u ξ).re ≤ ENNReal.ofReal (C + B0) := by
    have hmono : Monotone fun n => fun ξ => ENNReal.ofReal (g n ξ) := by
      intro n m hnm ξ
      by_cases hre : 0 ≤ (u ξ).re
      · apply ENNReal.ofReal_le_ofReal
        simp only [hg, hw]
        apply mul_le_mul_of_nonneg_left _ hre
        apply Real.exp_le_exp.mpr
        have : ((m : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := by
          apply inv_anti₀ (by positivity); exact_mod_cast Nat.add_le_add_right hnm 1
        nlinarith [sq_nonneg ξ]
      · push Not at hre
        have : g n ξ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hre.le (hw01 n ξ).1.le
        simp [ENNReal.ofReal_of_nonpos this]
    have hsup : ∀ ξ, ⨆ n, ENNReal.ofReal (g n ξ) = ENNReal.ofReal (u ξ).re := by
      intro ξ
      refine iSup_eq_of_tendsto (fun n m hnm => hmono hnm ξ) ?_
      refine ENNReal.tendsto_ofReal ?_
      have hw1 : Tendsto (fun n : ℕ => w n ξ) atTop (𝓝 1) := by
        have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
        have h2 : Tendsto (fun n : ℕ => -((n : ℝ) + 1)⁻¹ * ξ ^ 2) atTop (𝓝 0) := by
          simpa using h1.neg.mul_const (ξ ^ 2)
        have := (Real.continuous_exp.tendsto 0).comp h2
        simpa [hw, Function.comp_def] using this
      simpa using hw1.const_mul (u ξ).re
    calc ∫⁻ ξ in S, ENNReal.ofReal (u ξ).re = ∫⁻ ξ in S, ⨆ n, ENNReal.ofReal (g n ξ) := by simp_rw [hsup]
      _ = ⨆ n, ∫⁻ ξ in S, ENNReal.ofReal (g n ξ) := by
          refine lintegral_iSup (fun n => ?_) hmono
          exact ENNReal.measurable_ofReal.comp
            ((Complex.continuous_re.comp hu).mul (Real.continuous_exp.comp (by fun_prop))).measurable
      _ ≤ ENNReal.ofReal (C + B0) := by
          refine iSup_le (fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hgint n).integrableOn]
          · exact ENNReal.ofReal_le_ofReal (hSbound n)
          · filter_upwards [ae_restrict_mem hSm] with ξ hξ
            exact mul_nonneg (hR ξ hξ).2 (hw01 n ξ).1.le
  -- integrability on S and on its complement
  have hS1 : IntegrableOn u S := by
    refine ⟨hu.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ ξ in S, ‖u ξ‖ₑ = ∫⁻ ξ in S, ENNReal.ofReal (u ξ).re := by
          refine setLIntegral_congr_fun hSm (fun ξ hξ => ?_)
          obtain ⟨him, hre⟩ := hR ξ hξ
          have : ‖u ξ‖ = (u ξ).re := by
            rw [← Complex.re_add_im (u ξ), him]; simp [abs_of_nonneg hre]
          rw [← ofReal_norm, this]
      _ ≤ ENNReal.ofReal (C + B0) := hlin
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hS2 : IntegrableOn u Sᶜ := by
    rw [IntegrableOn, ← integrable_norm_iff hu.aestronglyMeasurable.restrict]; exact hcomp
  have := hS1.union hS2
  rwa [union_compl_self, integrableOn_univ] at this

/-! ## Fourier inversion almost everywhere -/

/-- Bump functions with radii `1/(n+2)` and `2/(n+2)`. -/
noncomputable def bumpN (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
    div_lt_div_of_pos_right (by norm_num) (by positivity)⟩

theorem bumpN_rOut_tendsto : Tendsto (fun n => (bumpN n).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have := (tendsto_inv_atTop_zero.comp h).const_mul 2
  simpa [bumpN, div_eq_mul_inv, Function.comp_def] using this

theorem bumpN_ratio (n : ℕ) : (bumpN n).rOut ≤ 2 * (bumpN n).rIn := by
  simp only [bumpN]; rw [mul_one_div]

/-- Convolution with a real kernel equals the complex convolution with its cast. -/
theorem conv_real_eq_complex (φ : ℝ → ℝ) (F : ℝ → ℂ) (x : ℝ) :
    (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x =
      ((fun t => (φ t : ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] F) x := by
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, Complex.real_smul, smul_eq_mul]

/-- The Fourier transform of a normed bump tends to `1`. -/
theorem tendsto_fourier_bump (ξ : ℝ) :
    Tendsto (fun n => 𝓕 (fun t => (((bumpN n).normed volume t : ℝ) : ℂ)) ξ) atTop (𝓝 1) := by
  have hg : Continuous (fun s : ℝ => ((𝐞 (s * ξ) : Circle) : ℂ)) := by fun_prop
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) bumpN_rOut_tendsto hg 0
  simp only [zero_mul, AddChar.map_zero_eq_one, Circle.coe_one] at h
  refine h.congr (fun n => ?_)
  rw [convolution_def, Real.fourier_real_eq]
  congr 1; ext t
  simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul, Circle.smul_def, smul_eq_mul, zero_sub, neg_mul]
  ring_nf

theorem norm_fourier_bump_le (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (fun t => (((bumpN n).normed volume t : ℝ) : ℂ)) ξ‖ ≤ 1 := by
  refine (norm_fourier_le ξ).trans (le_of_eq ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ContDiffBump.nonneg_normed _ _)]
  exact ContDiffBump.integral_normed _

/-- Fourier inversion almost everywhere: `F = 𝓕⁻ (𝓕 F)` a.e. for `F, 𝓕F ∈ L¹`. -/
theorem ae_eq_fourierInv {F : ℝ → ℂ} (hF : Integrable F) (hF' : Integrable (𝓕 F)) :
    F =ᵐ[volume] 𝓕⁻ (𝓕 F) := by
  set φ : ℕ → ℝ → ℝ := fun n => (bumpN n).normed volume with hφ
  set ψ : ℕ → ℝ → ℂ := fun n t => ((φ n t : ℝ) : ℂ) with hψ
  -- (1) the convolutions tend to F almost everywhere
  have h1 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (l := atTop)
    bumpN_rOut_tendsto (Eventually.of_forall bumpN_ratio) hF.locallyIntegrable
  -- (2) each convolution is the inverse transform of the product
  have hψint : ∀ n, Integrable (ψ n) := fun n =>
    (Complex.continuous_ofReal.comp (ContDiffBump.continuous_normed _)).integrable_of_hasCompactSupport
      ((ContDiffBump.hasCompactSupport_normed _).comp_left Complex.ofReal_zero)
  have h2 : ∀ n x, (φ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x =
      𝓕⁻ (fun ξ => 𝓕 (ψ n) ξ * 𝓕 F ξ) x := by
    intro n x
    rw [conv_real_eq_complex]
    set h := (ψ n) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] F with hh
    have hint : Integrable h := (hψint n).integrable_convolution _ hF
    have hcont : Continuous h :=
      ((ContDiffBump.hasCompactSupport_normed _).comp_left Complex.ofReal_zero).continuous_convolution_left _
        (Complex.continuous_ofReal.comp (ContDiffBump.continuous_normed _)) hF.locallyIntegrable
    have hFh : 𝓕 h = fun ξ => 𝓕 (ψ n) ξ * 𝓕 F ξ := by
      funext ξ
      rw [hh, Real.fourier_smul_convolution_eq (hψint n) hF ξ, smul_eq_mul]
    have hint' : Integrable (𝓕 h) := by
      rw [hFh]
      exact hF'.bdd_mul (c := 1) (continuous_fourier (hψint n)).aestronglyMeasurable
        (Eventually.of_forall fun ξ => norm_fourier_bump_le n ξ)
    have := hcont.fourierInv_fourier_eq hint hint'
    rw [← hFh]
    exact (congrFun this x).symm
  -- (3) the inverse transforms converge pointwise
  have h3 : ∀ x, Tendsto (fun n => 𝓕⁻ (fun ξ => 𝓕 (ψ n) ξ * 𝓕 F ξ) x) atTop (𝓝 (𝓕⁻ (𝓕 F) x)) := by
    intro x
    simp only [fourierInv_eq]
    refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕 F ξ‖) (fun n => ?_) hF'.norm
      (fun n => Eventually.of_forall fun ξ => ?_) (Eventually.of_forall fun ξ => ?_)
    · exact (by fun_prop : Continuous fun ξ : ℝ => (𝐞 (inner ℝ ξ x) : Circle)).aestronglyMeasurable.smul
        ((continuous_fourier (hψint n)).aestronglyMeasurable.mul hF'.aestronglyMeasurable)
    · rw [Circle.norm_smul, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_fourier_bump_le n ξ)
    · have := ((tendsto_fourier_bump ξ).mul_const (𝓕 F ξ)).const_smul (𝐞 (inner ℝ ξ x))
      simpa using this
  filter_upwards [h1] with x hx
  exact tendsto_nhds_unique (hx.congr (fun n => h2 n x)) (h3 x)

/-! ## `C_{6.11} ≥ A₊(1)²` -/

/-- A continuous function that is a.e. nonnegative on `{|x| ≥ r}` is nonnegative there. -/
theorem nonneg_of_ae_nonneg {g : ℝ → ℝ} (hg : Continuous g) {r : ℝ}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), r ≤ |x| → 0 ≤ g x) : ∀ x, r ≤ |x| → 0 ≤ g x := by
  have hopen : ∀ x, r < |x| → 0 ≤ g x := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have hVo : IsOpen ({y : ℝ | r < |y|} ∩ {y | g y < 0}) :=
      (isOpen_lt continuous_const continuous_abs).inter (isOpen_lt hg continuous_const)
    obtain ⟨y, hyV, hy⟩ := (Measure.dense_of_ae h).inter_open_nonempty _ hVo ⟨x, hx, hneg⟩
    exact absurd (hy hyV.1.le) (not_le.mpr hyV.2)
  intro x hx
  have hclosed : IsClosed {y | 0 ≤ g y} := isClosed_le continuous_const hg
  have hsub : {y : ℝ | r < |y|} ⊆ {y | 0 ≤ g y} := fun y hy => hopen y hy
  refine hclosed.closure_subset_iff.mpr hsub ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases le_or_gt 0 x with hx0 | hx0
  · refine ⟨x + ε / 2, ?_, ?_⟩
    · simp only [mem_ofPred_eq]
      rw [abs_of_nonneg (by linarith)]
      rw [abs_of_nonneg hx0] at hx; linarith
    · rw [Real.dist_eq, show x - (x + ε / 2) = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]; linarith
  · refine ⟨x - ε / 2, ?_, ?_⟩
    · simp only [mem_ofPred_eq]
      rw [abs_of_neg (by linarith)]
      rw [abs_of_neg hx0] at hx; linarith
    · rw [Real.dist_eq, show x - (x - ε / 2) = ε / 2 by ring, abs_of_pos (by linarith)]; linarith

/-- Lemma 2.4 of the paper (first part): `A₊(1)² ≤ C_{6.11}`. -/
theorem Aplus2_le_C611 : Aplus2 ≤ C611 := by
  unfold C611
  refine le_iInf₂ (fun f hf => ?_)
  have hA1 := A_pos_class611 hf
  obtain ⟨hint, hc0, heven, hf0, hft0⟩ := hf
  by_cases htop : A (ft f) = ⊤
  · rw [htop, ENNReal.mul_top hA1.ne']; exact le_top
  -- a tail of nonnegativity of `f̂`
  obtain ⟨R, -, hR⟩ : ∃ R, 0 < R ∧ ∀ ξ, R ≤ |ξ| → (ft f ξ).im = 0 ∧ 0 ≤ (ft f ξ).re := by
    have hlt : A (ft f) < ⊤ := lt_top_iff_ne_top.mpr htop
    unfold A at hlt
    obtain ⟨r, hr⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hr', _⟩ := iInf_lt_iff.mp hr
    exact ⟨r, hr'.1, hr'.2⟩
  set F : ℝ → ℂ := fun x => (f x : ℂ) with hFdef
  have hF : Integrable F := hint.ofReal
  have hF0 : ContinuousAt F 0 := Complex.continuous_ofReal.continuousAt.comp hc0
  have hFt : ft f = 𝓕 F := rfl
  have hFint : Integrable (𝓕 F) := integrable_fourier_of_nonneg_tail hF hF0 (by rw [← hFt]; exact hR)
  -- the continuous version `g` of `f`
  set g : ℝ → ℝ := fun x => (𝓕⁻ (𝓕 F) x).re with hgdef
  have hinvc : Continuous (𝓕⁻ (𝓕 F)) := by
    rw [fourierInv_eq_fourier_comp_neg]
    exact continuous_fourier (hFint.comp_neg)
  have hgc : Continuous g := Complex.continuous_re.comp hinvc
  have hae : F =ᵐ[volume] 𝓕⁻ (𝓕 F) := ae_eq_fourierInv hF hFint
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hae] with x hx
    show f x = (𝓕⁻ (𝓕 F) x).re
    rw [← hx]
    simp [hFdef]
  have hg0 : g 0 = f 0 := by
    simp only [hgdef]
    rw [hF.fourierInv_fourier_eq hFint hF0]
    simp [hFdef]
  have hftg : ft g = ft f := by
    funext ξ
    unfold ft
    apply fourier_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  have hgint : Integrable g := hint.congr hfg
  have hgeven : ∀ x, g (-x) = g x := by
    have hq := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hfg
    have h1 : (fun x => g (-x)) =ᵐ[volume] g := by
      filter_upwards [hq, hfg] with x hx1 hx2
      simp only [Function.comp_apply] at hx1
      rw [← hx1, heven x, hx2]
    have := (Continuous.ae_eq_iff_eq volume (hgc.comp continuous_neg) hgc).mp h1
    exact fun x => congrFun this x
  have hgA : ClassA g := by
    refine ⟨hgc, hgint, by rw [hftg, hFt]; exact hFint, hgeven, by rw [hg0]; exact hf0.le,
      by rw [hftg]; exact hft0.le, fun h => ?_⟩
    have := congrFun h 0
    simp only [Pi.zero_apply] at this
    rw [hg0] at this
    linarith
  have h1 : Aplus2 ≤ A (fun x => (g x : ℂ)) * A (ft g) := iInf₂_le g hgA
  have h2 : A (fun x => (g x : ℂ)) ≤ A (fun x => (f x : ℂ)) := by
    unfold A
    refine le_iInf₂ (fun r hr => iInf₂_le r ⟨hr.1, fun x hx => ⟨by simp, ?_⟩⟩)
    simp only [Complex.ofReal_re]
    refine nonneg_of_ae_nonneg hgc ?_ x hx
    filter_upwards [hfg] with y hy hry
    rw [← hy]
    simpa using (hr.2 y hry).2
  calc Aplus2 ≤ A (fun x => (g x : ℂ)) * A (ft g) := h1
    _ ≤ A (fun x => (f x : ℂ)) * A (ft f) := by rw [hftg]; gcongr

end SignUnc
