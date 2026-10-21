import SignUnc.Lower.Kappa

/-!
# Remark 2.3: `(S_r)` and `κ(r) < 1` give `A(f) A(f̂) > r²` on `𝒜`, hence `A₊(1)² ≥ r²`

Dilation to `A(f) = A(f̂) = τ`, then `g = f + f̂` (self-dual).  The paper's "nonzero" step (compact support of `f`
and `f̂`) is replaced by `κ(r) < 1`: an anti-self-dual `h` vanishing off `I` satisfies `h = -Kh` on `I`, so
`‖h‖ ≤ κ‖h‖` and `h = 0`.
-/

open MeasureTheory Real Set Filter Complex
open scoped FourierTransform ENNReal

namespace SignUnc

/-- `A(f) < |x|` gives `f(x)` real and nonnegative. -/
theorem nonneg_of_A_lt {f : ℝ → ℂ} {x : ℝ} (h : A f < ENNReal.ofReal |x|) : (f x).im = 0 ∧ 0 ≤ (f x).re := by
  unfold A at h
  obtain ⟨r, hr⟩ := iInf_lt_iff.mp h
  obtain ⟨hr', hlt⟩ := iInf_lt_iff.mp hr
  have hx : 0 < |x| := by
    by_contra h0; push_neg at h0
    rw [ENNReal.ofReal_of_nonpos h0] at hlt; exact (ENNReal.not_lt_zero hlt)
  have : r < |x| := (ENNReal.ofReal_lt_ofReal_iff hx).mp hlt
  exact hr'.2 x this.le

/-- The bound `|∫_I u Ku| ≤ κ ∫_I u²`. -/
theorem abs_integral_K_le {r κ : ℝ} (hκ0 : 0 ≤ κ)
    (hK : ∫ x in Icc (-r) r, (∫ t in Icc (-r) r, Real.cos (2 * π * x * t) ^ 2) ≤ κ ^ 2)
    {u : ℝ → ℝ} (hu : Continuous u) :
    |∫ x in Icc (-r) r, u x * (∫ t in Icc (-r) r, u t * Real.cos (2 * π * x * t))| ≤
      κ * ∫ x in Icc (-r) r, u x ^ 2 := by
  set I := Icc (-r) r
  have hIon : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f I := fun hf => hf.continuousOn.integrableOn_Icc
  set K : ℝ → ℝ := fun x => ∫ t in I, u t * Real.cos (2 * π * x * t) with hKdef
  have hKc : Continuous K := continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  set N2 := ∫ x in I, u x ^ 2 with hN2def
  have hN20 : 0 ≤ N2 := integral_nonneg (fun x => sq_nonneg _)
  set M2 : ℝ → ℝ := fun x => ∫ t in I, Real.cos (2 * π * x * t) ^ 2 with hM2def
  have hM2c : Continuous M2 := continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have ha : ∀ x, K x ^ 2 ≤ N2 * M2 x := fun x =>
    sq_integral_mul_le (hIon (hu.pow 2)) (hIon (by fun_prop)) (hIon (by fun_prop))
  have hb : ∫ x in I, K x ^ 2 ≤ N2 * κ ^ 2 := by
    calc ∫ x in I, K x ^ 2 ≤ ∫ x in I, N2 * M2 x :=
          setIntegral_mono_on (hIon (hKc.pow 2)) (hIon (continuous_const.mul hM2c)) measurableSet_Icc
            (fun x _ => ha x)
      _ = N2 * ∫ x in I, M2 x := integral_const_mul _ _
      _ ≤ N2 * κ ^ 2 := mul_le_mul_of_nonneg_left hK hN20
  apply abs_le_of_sq_le (mul_nonneg hκ0 hN20)
  calc (∫ x in I, u x * K x) ^ 2 ≤ N2 * ∫ x in I, K x ^ 2 :=
        sq_integral_mul_le (hIon (hu.pow 2)) (hIon (hKc.pow 2)) (hIon (hu.mul hKc))
    _ ≤ N2 * (N2 * κ ^ 2) := mul_le_mul_of_nonneg_left hb hN20
    _ = (κ * N2) ^ 2 := by ring

/-- An even real integrable `h` with `ĥ = -h` that vanishes off `I` is zero, when `κ < 1`. -/
theorem antiselfdual_zero {r κ : ℝ} (hr : 0 < r) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hK : ∫ x in Icc (-r) r, (∫ t in Icc (-r) r, Real.cos (2 * π * x * t) ^ 2) ≤ κ ^ 2)
    {h : ℝ → ℝ} (hc : Continuous h) (hi : Integrable h) (he : ∀ x, h (-x) = h x)
    (hft : ft h = fun x => ((-h x : ℝ) : ℂ)) (hO : ∀ x, x ∉ Icc (-r) r → h x = 0) : h = 0 := by
  set I := Icc (-r) r with hIdef
  have hIon : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f I := fun hf => hf.continuousOn.integrableOn_Icc
  -- `h = -Kh` everywhere
  have hK' : ∀ x, h x = -∫ t in I, h t * Real.cos (2 * π * x * t) := by
    intro x
    have h1 := ft_even hi he x
    rw [hft] at h1
    simp only at h1
    have h2 : -h x = cosT h x := by exact_mod_cast h1
    have h3 : cosT h x = ∫ t in I, h t * Real.cos (2 * π * x * t) := by
      unfold cosT
      rw [← integral_add_compl measurableSet_Icc (integrable_mul_cos hi x)]
      have : ∫ t in Iᶜ, h t * Real.cos (2 * π * x * t) = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
        rw [hO t ht, zero_mul]
      rw [this, add_zero]
    linarith
  set N2 := ∫ x in I, h x ^ 2 with hN2def
  have hN20 : 0 ≤ N2 := integral_nonneg (fun x => sq_nonneg _)
  have hN2eq : N2 = -∫ x in I, h x * (∫ t in I, h t * Real.cos (2 * π * x * t)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
    show h x ^ 2 = -(h x * ∫ t in I, h t * Real.cos (2 * π * x * t))
    have := hK' x
    rw [sq]
    nth_rewrite 2 [this]
    ring
  have hb := abs_integral_K_le hκ0 hK hc
  rw [← hN2def] at hb
  have hz : N2 = 0 := by
    have := neg_abs_le (∫ x in I, h x * (∫ t in I, h t * Real.cos (2 * π * x * t)))
    have h2 : N2 ≤ κ * N2 := by linarith
    nlinarith
  have hae2 : (fun x => h x ^ 2) =ᵐ[volume.restrict I] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Icc (fun x _ => sq_nonneg (h x)))
      (hIon (hc.pow 2))).mp hz
  have hae : h =ᵐ[volume.restrict I] 0 := by
    filter_upwards [hae2] with x hx
    simpa using hx
  have hsub : I ⊆ closure (interior I) := by
    rw [hIdef, interior_Icc, closure_Ioo (by linarith)]
  have hI := Measure.eqOn_of_ae_eq hae hc.continuousOn continuousOn_const hsub
  funext x
  by_cases hx : x ∈ I
  · exact hI hx
  · exact hO x hx

/-- Dilation of the cosine transform: `cosT (f(c·)) ξ = c⁻¹ cosT f (ξ/c)` for `c > 0`. -/
theorem cosT_comp_mul (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    cosT (fun x => f (c * x)) ξ = c⁻¹ * cosT f (ξ / c) := by
  unfold cosT
  have := Measure.integral_comp_mul_left (fun u => f u * Real.cos (2 * π * (ξ / c) * u)) c
  simp only [smul_eq_mul] at this
  rw [abs_of_pos (inv_pos.mpr hc)] at this
  rw [← this]
  congr 1; funext x
  congr 2; field_simp

theorem cosT_neg (f : ℝ → ℝ) (ξ : ℝ) : cosT f (-ξ) = cosT f ξ := by
  unfold cosT; congr 1; funext t; rw [show 2 * π * -ξ * t = -(2 * π * ξ * t) by ring, Real.cos_neg]

/-- For `f` in `𝒜`, the cosine transform `F` satisfies `f̂ = F` and `F̂ = f`. -/
theorem classA_dual {f : ℝ → ℝ} (hcont : Continuous f) (hint : Integrable f) (hint' : Integrable (ft f))
    (heven : ∀ x, f (-x) = f x) :
    ft f = (fun ξ => ((cosT f ξ : ℝ) : ℂ)) ∧ Integrable (cosT f) ∧ Continuous (cosT f) ∧
      ft (cosT f) = (fun x => ((f x : ℝ) : ℂ)) := by
  have h1 : ft f = (fun ξ => ((cosT f ξ : ℝ) : ℂ)) := funext fun ξ => ft_even hint heven ξ
  have hFi : Integrable (cosT f) := by
    have := hint'.re; rw [h1] at this; simpa using this
  have hFc : Continuous (cosT f) := by
    have := Complex.continuous_re.comp (continuous_ft hint); rw [h1] at this
    simpa [Function.comp_def] using this
  refine ⟨h1, hFi, hFc, ?_⟩
  have hinv : 𝓕⁻ (ft f) = fun x => ((f x : ℝ) : ℂ) :=
    Continuous.fourierInv_fourier_eq (Complex.continuous_ofReal.comp hcont) hint.ofReal hint'
  rw [h1, fourierInv_eq_fourier_comp_neg] at hinv
  simp only [cosT_neg] at hinv
  exact hinv

/-- Remark 2.3: `(S_r)` and `κ(r) < 1` give `r² ≤ A(f) A(f̂)` on `𝒜`. -/
theorem le_A_mul_of_Sr {r κ : ℝ} (hr : 0 < r) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hK : ∫ x in Icc (-r) r, (∫ t in Icc (-r) r, Real.cos (2 * π * x * t) ^ 2) ≤ κ ^ 2)
    (hS : Sr r) {f : ℝ → ℝ} (hf : ClassA f) :
    ENNReal.ofReal (r ^ 2) ≤ A (fun x => (f x : ℂ)) * A (ft f) := by
  have hApos := A_pos_classA hf
  have hBpos := A_ft_pos_classA hf
  obtain ⟨hcont, hint, hint', heven, h0, hft0, hne⟩ := hf
  obtain ⟨hFT, hFi, hFc, hFF⟩ := classA_dual hcont hint hint' heven
  set F := cosT f with hFdef
  -- infinite cases
  by_cases ha : A (fun x => (f x : ℂ)) = ⊤
  · rw [ha, ENNReal.top_mul hBpos.ne']; exact le_top
  by_cases hb : A (ft f) = ⊤
  · rw [hb, ENNReal.mul_top hApos.ne']; exact le_top
  set α := (A (fun x => (f x : ℂ))).toReal with hα
  set β := (A (ft f)).toReal with hβ
  have hαA : A (fun x => (f x : ℂ)) = ENNReal.ofReal α := (ENNReal.ofReal_toReal ha).symm
  have hβA : A (ft f) = ENNReal.ofReal β := (ENNReal.ofReal_toReal hb).symm
  have hα0 : 0 < α := ENNReal.toReal_pos hApos.ne' ha
  have hβ0 : 0 < β := ENNReal.toReal_pos hBpos.ne' hb
  rw [hαA, hβA, ← ENNReal.ofReal_mul hα0.le]
  apply ENNReal.ofReal_le_ofReal
  by_contra hlt
  push_neg at hlt
  -- dilation
  set lam := Real.sqrt (α / β) with hlam
  set τ := Real.sqrt (α * β) with hτ
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr (div_pos hα0 hβ0)
  have hτ0 : 0 < τ := Real.sqrt_pos.mpr (mul_pos hα0 hβ0)
  have hlamτ : lam * τ = α := by
    rw [hlam, hτ, ← Real.sqrt_mul (div_pos hα0 hβ0).le, show α / β * (α * β) = α ^ 2 by field_simp]
    exact Real.sqrt_sq hα0.le
  have hlamβ : lam * β = τ := by
    rw [hlam, hτ]
    rw [show α * β = (α / β) * β ^ 2 by field_simp, Real.sqrt_mul (div_pos hα0 hβ0).le, Real.sqrt_sq hβ0.le]
  have hτr : τ ≤ r := by
    rw [hτ]; calc Real.sqrt (α * β) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hlt.le
      _ = r := Real.sqrt_sq hr.le
  -- nonnegativity of `f` beyond `α` and of `F` beyond `β`
  have hfpos : ∀ x, α < |x| → 0 ≤ f x := by
    intro x hx
    have : A (fun x => (f x : ℂ)) < ENNReal.ofReal |x| := by
      rw [hαA]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hx
    simpa using (nonneg_of_A_lt this).2
  have hFpos : ∀ ξ, β < |ξ| → 0 ≤ F ξ := by
    intro ξ hξ
    have : A (ft f) < ENNReal.ofReal |ξ| := by
      rw [hβA]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hξ
    have h2 := (nonneg_of_A_lt this).2
    rw [hFT] at h2; simpa using h2
  -- the pieces
  set h1 : ℝ → ℝ := fun x => f (lam * x) with hh1
  set h2 : ℝ → ℝ := fun x => lam⁻¹ * F (lam⁻¹ * x) with hh2
  have hh1c : Continuous h1 := hcont.comp (continuous_const.mul continuous_id)
  have hh2c : Continuous h2 := continuous_const.mul (hFc.comp (continuous_const.mul continuous_id))
  have hh1i : Integrable h1 := hint.comp_mul_left' hlam0.ne'
  have hh2i : Integrable h2 := (hFi.comp_mul_left' (inv_ne_zero hlam0.ne')).const_mul _
  have hh1e : ∀ x, h1 (-x) = h1 x := fun x => by simp only [hh1, mul_neg, heven]
  have hh2e : ∀ x, h2 (-x) = h2 x := fun x => by
    simp only [hh2, mul_neg]; rw [show F (-(lam⁻¹ * x)) = F (lam⁻¹ * x) from cosT_neg f _]
  have hcosF : ∀ x, cosT F x = f x := by
    intro x
    have := ft_even hFi (cosT_neg f) x
    rw [hFF] at this
    simp only at this
    exact_mod_cast this.symm
  have hcos1 : ∀ ξ, cosT h1 ξ = h2 ξ := by
    intro ξ
    rw [cosT_comp_mul f hlam0 ξ]
    simp only [hh2, hFdef]; rw [div_eq_inv_mul]
  have hcos2 : ∀ ξ, cosT h2 ξ = h1 ξ := by
    intro ξ
    have e : cosT h2 ξ = lam⁻¹ * cosT (fun x => F (lam⁻¹ * x)) ξ := by
      unfold cosT; simp only [hh2, mul_assoc]; rw [integral_const_mul]
    rw [e, cosT_comp_mul F (inv_pos.mpr hlam0) ξ, inv_inv, div_inv_eq_mul, hcosF]
    simp only [hh1]; rw [← mul_assoc, inv_mul_cancel₀ hlam0.ne', one_mul, mul_comm]
  -- `g = h1 + h2` is self-dual, nonnegative beyond `r`, `g(0) ≤ 0`
  set g : ℝ → ℝ := fun x => h1 x + h2 x with hgdef
  have hgi : Integrable g := hh1i.add hh2i
  have hge : ∀ x, g (-x) = g x := fun x => by simp only [hgdef, hh1e, hh2e]
  have hgft : ft g = fun x => ((g x : ℝ) : ℂ) := by
    funext ξ
    rw [ft_even hgi hge ξ]
    congr 1
    unfold cosT
    simp only [hgdef, add_mul]
    rw [integral_add (integrable_mul_cos hh1i ξ) (integrable_mul_cos hh2i ξ)]
    change cosT h1 ξ + cosT h2 ξ = h1 ξ + h2 ξ
    rw [hcos1, hcos2, add_comm]
  have hF0 : F 0 ≤ 0 := by
    have := hft0; rw [hFT] at this; simpa using this
  have hg0 : g 0 ≤ 0 := by
    simp only [hgdef, hh1, hh2, mul_zero]
    have : 0 ≤ lam⁻¹ := (inv_pos.mpr hlam0).le
    nlinarith
  have h1pos : ∀ x, τ < |x| → 0 ≤ h1 x := by
    intro x hx
    apply hfpos
    rw [abs_mul, abs_of_pos hlam0, ← hlamτ]
    exact mul_lt_mul_of_pos_left hx hlam0
  have h2pos : ∀ x, τ < |x| → 0 ≤ h2 x := by
    intro x hx
    apply mul_nonneg (inv_pos.mpr hlam0).le
    apply hFpos
    rw [abs_mul, abs_of_pos (inv_pos.mpr hlam0)]
    rw [← hlamβ] at hx
    rw [lt_inv_mul_iff₀ hlam0]
    linarith
  have hgpos : ∀ x, r < |x| → 0 ≤ g x := fun x hx =>
    add_nonneg (h1pos x (by linarith)) (h2pos x (by linarith))
  have hgz := hS g (hh1c.add hh2c) hgi hge hgft hg0 hgpos
  -- then `h1` is anti-self-dual and vanishes off `I`
  have h12 : ∀ x, h2 x = -h1 x := fun x => by
    have := congrFun hgz x; simp only [hgdef, Pi.zero_apply] at this; linarith
  have h1O : ∀ x, x ∉ Icc (-r) r → h1 x = 0 := by
    intro x hx
    have hxr : r < |x| := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact hx
    have := h2pos x (by linarith)
    rw [h12] at this
    linarith [h1pos x (by linarith)]
  have h1ft : ft h1 = fun x => ((-h1 x : ℝ) : ℂ) := by
    funext ξ; rw [ft_even hh1i hh1e ξ, hcos1, h12]
  have h1z := antiselfdual_zero hr hκ0 hκ1 hK hh1c hh1i hh1e h1ft h1O
  apply hne
  funext y
  have := congrFun h1z (lam⁻¹ * y)
  simp only [hh1, Pi.zero_apply] at this
  rw [← mul_assoc, mul_inv_cancel₀ hlam0.ne', one_mul] at this
  simpa using this

/-- `(S_r)` and `κ(r) < 1` give `A₊(1)² ≥ r²`. -/
theorem Aplus2_ge_of_Sr {r κ : ℝ} (hr : 0 < r) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hK : ∫ x in Icc (-r) r, (∫ t in Icc (-r) r, Real.cos (2 * π * x * t) ^ 2) ≤ κ ^ 2)
    (hS : Sr r) : ENNReal.ofReal (r ^ 2) ≤ Aplus2 :=
  le_iInf₂ fun _ hf => le_A_mul_of_Sr hr hκ0 hκ1 hK hS hf

end SignUnc
