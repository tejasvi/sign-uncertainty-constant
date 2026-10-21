import SignUnc.Lower.Identity

/-!
# Lemma 3.3: the a priori bound `‖g‖_{L²(I)} (1 - κ) ≤ √(2r) ∫_O g`

Elementary form: `g = Kg + h` on `I`, `|h| ≤ P`, Cauchy–Schwarz (by the discriminant) pointwise and on `I`, and the
iterated integral `∫_I ∫_I cos²(2πxt) dt dx ≤ κ²`.
-/

open MeasureTheory Real Set Filter

namespace SignUnc

/-- Cauchy–Schwarz for integrals, from the discriminant of `t ↦ ∫ (f - t g)²`. -/
theorem sq_integral_mul_le {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  set A := ∫ x, f x ^ 2 ∂μ
  set B := ∫ x, f x * g x ∂μ
  set Cc := ∫ x, g x ^ 2 ∂μ
  have hq : ∀ t : ℝ, 0 ≤ Cc * (t * t) + (-2 * B) * t + A := by
    intro t
    have h0 : 0 ≤ ∫ x, (f x - t * g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have e1 : (fun x => (f x - t * g x) ^ 2) = fun x => f x ^ 2 - (2 * t) * (f x * g x) + t ^ 2 * g x ^ 2 := by
      funext x; ring
    have e : ∫ x, (f x - t * g x) ^ 2 ∂μ = A - 2 * t * B + t ^ 2 * Cc := by
      rw [e1, integral_add, integral_sub, integral_const_mul, integral_const_mul]
      · exact hf
      · exact hfg.const_mul _
      · exact hf.sub (hfg.const_mul _)
      · exact hg.const_mul _
    nlinarith
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

theorem abs_le_of_sq_le {X c : ℝ} (hc : 0 ≤ c) (h : X ^ 2 ≤ c ^ 2) : |X| ≤ c := by
  by_contra hlt
  push_neg at hlt
  have : c ^ 2 < |X| ^ 2 := by nlinarith [abs_nonneg X]
  rw [sq_abs] at this
  linarith

/-- Lemma 3.3 of the paper, elementary form: `‖g‖_{L²(I)} (1 - κ) ≤ √(2r) ∫_O g`. -/
theorem apriori {r κ : ℝ} (hr : 0 < r) (hκ1 : κ < 1) (hκ0 : 0 ≤ κ)
    (hK : ∫ x in Icc (-r) r, (∫ t in Icc (-r) r, Real.cos (2 * π * x * t) ^ 2) ≤ κ ^ 2)
    {g : ℝ → ℝ} (hc : Continuous g) (hi : Integrable g) (he : ∀ x, g (-x) = g x)
    (hft : ft g = fun x => (g x : ℂ)) (hO : ∀ x, x ∉ Icc (-r) r → 0 ≤ g x) :
    Real.sqrt (∫ x in Icc (-r) r, g x ^ 2) * (1 - κ) ≤ Real.sqrt (2 * r) * ∫ y in (Icc (-r) r)ᶜ, g y := by
  set I := Icc (-r) r with hIdef
  set P := ∫ y in Iᶜ, g y with hPdef
  have hIon : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f I := fun hf => hf.continuousOn.integrableOn_Icc
  set K : ℝ → ℝ := fun x => ∫ t in I, g t * Real.cos (2 * π * x * t) with hKdef
  set H : ℝ → ℝ := fun x => ∫ t in Iᶜ, g t * Real.cos (2 * π * x * t) with hHdef
  have hgKH : ∀ x, g x = K x + H x := by
    intro x
    rw [eval_eq_cosT hi he hft x]
    unfold cosT
    exact (integral_add_compl measurableSet_Icc (integrable_mul_cos hi x)).symm
  have hKc : Continuous K := continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have hHc : Continuous H := by
    have : H = fun x => g x - K x := by funext x; rw [hgKH x]; ring
    rw [this]; exact hc.sub hKc
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Icc.compl (fun x hx => hO x hx)
  have hHle : ∀ x, |H x| ≤ P := by
    intro x
    calc |H x| ≤ ∫ t in Iᶜ, |g t * Real.cos (2 * π * x * t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Iᶜ, g t := by
        refine setIntegral_mono_on (integrable_mul_cos hi x).abs.integrableOn hi.integrableOn
          measurableSet_Icc.compl (fun t ht => ?_)
        rw [abs_mul, abs_of_nonneg (hO t ht)]
        have := Real.abs_cos_le_one (2 * π * x * t)
        have := hO t ht
        nlinarith [abs_nonneg (Real.cos (2 * π * x * t))]
  set N2 := ∫ x in I, g x ^ 2 with hN2def
  have hN20 : 0 ≤ N2 := integral_nonneg (fun x => sq_nonneg _)
  -- `(K x)² ≤ N2 ∫_I cos²(2πx·)`
  set M2 : ℝ → ℝ := fun x => ∫ t in I, Real.cos (2 * π * x * t) ^ 2 with hM2def
  have hM2c : Continuous M2 := continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have ha : ∀ x, K x ^ 2 ≤ N2 * M2 x := by
    intro x
    exact sq_integral_mul_le (hIon (hc.pow 2)) (hIon (by fun_prop)) (hIon (by fun_prop))
  have hb : ∫ x in I, K x ^ 2 ≤ N2 * κ ^ 2 := by
    calc ∫ x in I, K x ^ 2 ≤ ∫ x in I, N2 * M2 x :=
          setIntegral_mono_on (hIon (hKc.pow 2)) (hIon (continuous_const.mul hM2c)) measurableSet_Icc
            (fun x _ => ha x)
      _ = N2 * ∫ x in I, M2 x := integral_const_mul _ _
      _ ≤ N2 * κ ^ 2 := mul_le_mul_of_nonneg_left hK hN20
  -- `N2 = ∫_I g K + ∫_I g H`
  have hc' : N2 = (∫ x in I, g x * K x) + ∫ x in I, g x * H x := by
    have hsum := integral_add (μ := volume.restrict I) (f := fun x => g x * K x) (g := fun x => g x * H x)
      (hIon (hc.mul hKc)) (hIon (hc.mul hHc))
    rw [← hsum]
    refine setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
    show g x ^ 2 = g x * K x + g x * H x
    rw [sq, ← mul_add, ← hgKH x]
  -- `|∫_I g K| ≤ κ N2`
  have hd : |∫ x in I, g x * K x| ≤ N2 * κ := by
    apply abs_le_of_sq_le (mul_nonneg hN20 hκ0)
    calc (∫ x in I, g x * K x) ^ 2 ≤ N2 * ∫ x in I, K x ^ 2 :=
          sq_integral_mul_le (hIon (hc.pow 2)) (hIon (hKc.pow 2)) (hIon (hc.mul hKc))
      _ ≤ N2 * (N2 * κ ^ 2) := mul_le_mul_of_nonneg_left hb hN20
      _ = (N2 * κ) ^ 2 := by ring
  -- `|∫_I g H| ≤ P √(2r) √N2`
  have hmeas : ∫ x in I, (1 : ℝ) ^ 2 = 2 * r := by
    simp only [one_pow, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul,
      mul_one, I, Real.volume_real_Icc]
    rw [max_eq_left (by linarith)]; ring
  have habs : ∫ x in I, |g x| ≤ Real.sqrt (2 * r) * Real.sqrt N2 := by
    rw [← Real.sqrt_mul (by linarith)]
    apply Real.le_sqrt_of_sq_le
    have := sq_integral_mul_le (μ := volume.restrict I) (f := fun x => |g x|) (g := fun _ => (1 : ℝ))
      (hIon ((continuous_abs.comp hc).pow 2)) (hIon continuous_const) (hIon ((continuous_abs.comp hc).mul continuous_const))
    simp only [mul_one, sq_abs] at this
    rw [hmeas, ← hN2def] at this
    linarith
  have he' : |∫ x in I, g x * H x| ≤ P * (Real.sqrt (2 * r) * Real.sqrt N2) := by
    calc |∫ x in I, g x * H x| ≤ ∫ x in I, |g x * H x| := abs_integral_le_integral_abs
      _ ≤ ∫ x in I, P * |g x| := by
          refine setIntegral_mono_on (hIon (continuous_abs.comp (hc.mul hHc))) (hIon (continuous_const.mul
            (continuous_abs.comp hc))) measurableSet_Icc (fun x _ => ?_)
          rw [abs_mul, mul_comm P]
          exact mul_le_mul_of_nonneg_left (hHle x) (abs_nonneg _)
      _ = P * ∫ x in I, |g x| := integral_const_mul _ _
      _ ≤ P * (Real.sqrt (2 * r) * Real.sqrt N2) := mul_le_mul_of_nonneg_left habs hP0
  -- combine
  have hf : N2 ≤ κ * N2 + P * Real.sqrt (2 * r) * Real.sqrt N2 := by
    have h1 := le_abs_self (∫ x in I, g x * K x)
    have h2 := le_abs_self (∫ x in I, g x * H x)
    nlinarith
  set sN := Real.sqrt N2 with hsN
  have hsq : sN ^ 2 = N2 := Real.sq_sqrt hN20
  have hs0 : 0 ≤ sN := Real.sqrt_nonneg _
  have h2r : 0 ≤ Real.sqrt (2 * r) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · rw [← h0]; simp only [zero_mul]; exact mul_nonneg h2r hP0
  · have : sN * (sN * (1 - κ)) ≤ sN * (Real.sqrt (2 * r) * P) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

end SignUnc
