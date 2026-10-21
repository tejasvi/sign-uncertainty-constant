import SignUnc.Lower.Criterion

/-!
# `κ(r) < 1`: the iterated integral `∫_I ∫_I cos²(2πxt) dt dx`

`cos²θ ≤ 1 - (θ - θ³/6)²` for `θ² ≤ 6` (from `sin θ > θ - θ³/6`), then exact polynomial integrals and the
six-digit bounds of `π`.
-/

open MeasureTheory Real Set Filter

namespace SignUnc

theorem cos_sq_le_poly {θ : ℝ} (hθ : θ ^ 2 ≤ 6) : Real.cos θ ^ 2 ≤ 1 - (θ - θ ^ 3 / 6) ^ 2 := by
  have key : ∀ u : ℝ, 0 ≤ u → u ^ 2 ≤ 6 → (u - u ^ 3 / 6) ^ 2 ≤ Real.sin u ^ 2 := by
    intro u hu hu6
    rcases eq_or_lt_of_le hu with h0 | hpos
    · subst h0; simp
    · have h1 := Real.sin_gt_sub_cube hpos
      have h2 : 0 ≤ u - u ^ 3 / 6 := by nlinarith
      exact pow_le_pow_left₀ h2 h1.le 2
  have hsin : (θ - θ ^ 3 / 6) ^ 2 ≤ Real.sin θ ^ 2 := by
    rcases le_or_gt 0 θ with h | h
    · exact key θ h hθ
    · have := key (-θ) (by linarith) (by nlinarith)
      rw [Real.sin_neg] at this
      nlinarith
  have := Real.sin_sq_add_cos_sq θ
  linarith

/-- `∫_{-r}^{r} (a₀ - a₁t² + a₂t⁴ - a₃t⁶) dt`. -/
theorem setIntegral_Icc_poly (r : ℝ) (hr : 0 ≤ r) (a0 a1 a2 a3 : ℝ) :
    ∫ t in Icc (-r) r, (a0 - a1 * t ^ 2 + a2 * t ^ 4 - a3 * t ^ 6) =
      2 * r * a0 - a1 * (2 * r ^ 3 / 3) + a2 * (2 * r ^ 5 / 5) - a3 * (2 * r ^ 7 / 7) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hF : ∀ t ∈ uIcc (-r) r, HasDerivAt (fun t => a0 * t - a1 * (t ^ 3 / 3) + a2 * (t ^ 5 / 5) - a3 * (t ^ 7 / 7))
      (a0 - a1 * t ^ 2 + a2 * t ^ 4 - a3 * t ^ 6) t := by
    intro t _
    have := ((((hasDerivAt_id t).const_mul a0).sub (((hasDerivAt_pow 3 t).div_const 3).const_mul a1)).add
      (((hasDerivAt_pow 5 t).div_const 5).const_mul a2)).sub (((hasDerivAt_pow 7 t).div_const 7).const_mul a3)
    refine this.congr_deriv ?_
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (by
    apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- The polynomial majorant `1 - θ² + θ⁴/3 - θ⁶/36` of `cos²θ`, integrated. -/
theorem kappa_sq_le {r : ℝ} (hr : 0 < r) (hr6 : (2 * π * r ^ 2) ^ 2 ≤ 6) :
    ∫ x in Icc (-r) r, (∫ t in Icc (-r) r, Real.cos (2 * π * x * t) ^ 2) ≤
      4 * r ^ 2 - (2 * π) ^ 2 * (2 * r ^ 3 / 3) ^ 2 + (2 * π) ^ 4 * (2 * r ^ 5 / 5) ^ 2 / 3 -
        (2 * π) ^ 6 * (2 * r ^ 7 / 7) ^ 2 / 36 := by
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * π := ⟨_, rfl⟩
  rw [← hc] at hr6 ⊢
  have hIon : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f (Icc (-r) r) := fun hf => hf.continuousOn.integrableOn_Icc
  have hbound : ∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (-r) r, (c * x * t) ^ 2 ≤ 6 := by
    intro x hx t ht
    have hx' : x ^ 2 ≤ r ^ 2 := by nlinarith [hx.1, hx.2]
    have ht' : t ^ 2 ≤ r ^ 2 := by nlinarith [ht.1, ht.2]
    have h1 : x ^ 2 * t ^ 2 ≤ r ^ 2 * r ^ 2 := mul_le_mul hx' ht' (sq_nonneg _) (sq_nonneg _)
    have h2 : (c * x * t) ^ 2 = c ^ 2 * (x ^ 2 * t ^ 2) := by ring
    have h3 : (c * r ^ 2) ^ 2 = c ^ 2 * (r ^ 2 * r ^ 2) := by ring
    have h4 : c ^ 2 * (x ^ 2 * t ^ 2) ≤ c ^ 2 * (r ^ 2 * r ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    linarith
  -- inner bound
  have hinner : ∀ x ∈ Icc (-r) r, ∫ t in Icc (-r) r, Real.cos (c * x * t) ^ 2 ≤
      2 * r - c ^ 2 * x ^ 2 * (2 * r ^ 3 / 3) + c ^ 4 * x ^ 4 * (2 * r ^ 5 / 5) / 3 -
        c ^ 6 * x ^ 6 * (2 * r ^ 7 / 7) / 36 := by
    intro x hx
    have hp : ∀ t, 1 - (c * x * t - (c * x * t) ^ 3 / 6) ^ 2 =
        1 - c ^ 2 * x ^ 2 * t ^ 2 + c ^ 4 * x ^ 4 / 3 * t ^ 4 - c ^ 6 * x ^ 6 / 36 * t ^ 6 := by
      intro t; ring
    calc ∫ t in Icc (-r) r, Real.cos (c * x * t) ^ 2 ≤ ∫ t in Icc (-r) r, (1 - (c * x * t - (c * x * t) ^ 3 / 6) ^ 2) :=
          setIntegral_mono_on (hIon (by fun_prop)) (hIon (by fun_prop)) measurableSet_Icc
            (fun t ht => cos_sq_le_poly (hbound x hx t ht))
      _ = ∫ t in Icc (-r) r, (1 - c ^ 2 * x ^ 2 * t ^ 2 + c ^ 4 * x ^ 4 / 3 * t ^ 4 -
            c ^ 6 * x ^ 6 / 36 * t ^ 6) := by simp_rw [hp]
      _ = 2 * r - c ^ 2 * x ^ 2 * (2 * r ^ 3 / 3) + c ^ 4 * x ^ 4 * (2 * r ^ 5 / 5) / 3 -
            c ^ 6 * x ^ 6 * (2 * r ^ 7 / 7) / 36 := by
        rw [setIntegral_Icc_poly r hr.le]; ring
  calc ∫ x in Icc (-r) r, (∫ t in Icc (-r) r, Real.cos (c * x * t) ^ 2)
      ≤ ∫ x in Icc (-r) r, (2 * r - c ^ 2 * x ^ 2 * (2 * r ^ 3 / 3) + c ^ 4 * x ^ 4 * (2 * r ^ 5 / 5) / 3 -
          c ^ 6 * x ^ 6 * (2 * r ^ 7 / 7) / 36) := by
        refine setIntegral_mono_on ?_ (hIon (by fun_prop)) measurableSet_Icc hinner
        exact hIon (continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc)
    _ = 4 * r ^ 2 - c ^ 2 * (2 * r ^ 3 / 3) ^ 2 + c ^ 4 * (2 * r ^ 5 / 5) ^ 2 / 3 - c ^ 6 * (2 * r ^ 7 / 7) ^ 2 / 36 := by
        have hp : ∀ x : ℝ, 2 * r - c ^ 2 * x ^ 2 * (2 * r ^ 3 / 3) + c ^ 4 * x ^ 4 * (2 * r ^ 5 / 5) / 3 -
            c ^ 6 * x ^ 6 * (2 * r ^ 7 / 7) / 36 = 2 * r - (c ^ 2 * (2 * r ^ 3 / 3)) * x ^ 2 +
              (c ^ 4 * (2 * r ^ 5 / 5) / 3) * x ^ 4 - (c ^ 6 * (2 * r ^ 7 / 7) / 36) * x ^ 6 := by
          intro x; ring
        simp_rw [hp]
        rw [setIntegral_Icc_poly r hr.le]; ring

/-- `κ(2751/5000)² ≤ 0.90307 = 0.9503²`. -/
theorem kappa_r0 : ∫ x in Icc (-(2751 / 5000 : ℝ)) (2751 / 5000),
    (∫ t in Icc (-(2751 / 5000 : ℝ)) (2751 / 5000), Real.cos (2 * π * x * t) ^ 2) ≤ (9503 / 10000 : ℝ) ^ 2 := by
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  have hr6 : (2 * π * (2751 / 5000 : ℝ) ^ 2) ^ 2 ≤ 6 := by nlinarith
  refine (kappa_sq_le (by norm_num) hr6).trans ?_
  -- monotone pieces in `π`
  have h2 : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hlo.le 2
  have h4 : π ^ 4 ≤ (3.141593 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) hhi.le 4
  have h6 : (3.141592 : ℝ) ^ 6 ≤ π ^ 6 := pow_le_pow_left₀ (by norm_num) hlo.le 6
  have e : ∀ x : ℝ, (2 * x) ^ 2 = 4 * x ^ 2 ∧ (2 * x) ^ 4 = 16 * x ^ 4 ∧ (2 * x) ^ 6 = 64 * x ^ 6 := fun x =>
    ⟨by ring, by ring, by ring⟩
  rw [(e π).1, (e π).2.1, (e π).2.2]
  nlinarith

end SignUnc
