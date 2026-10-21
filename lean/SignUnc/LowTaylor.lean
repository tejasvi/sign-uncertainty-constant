import SignUnc.LowSound1
import SignUnc.TaylorK

/-!
# Taylor bounds for `e^{ix}` and `cos x` (all real `x`)

`|Re/Im (e^{ix} - Σ_{n<N} (ix)^n/n!)| ≤ |x|^N/N!` (two-sided Taylor bound on the chains `Re(e^{it}(i)^j)/j!`),
hence `|e^{ix} - Σ_{n<N} (ix)^n/n!| ≤ 2|x|^N/N!` and `|cos x - Σ_{n<N} (-1)^n x^{2n}/(2n)!| ≤ |x|^{2N}/(2N)!`.
-/

namespace SignUnc

open Real Complex Finset

/-- `Re(K e^{it} i^j / j!)` for `K ∈ {1, -i}` as a chain of normalized Taylor coefficients. -/
theorem taylor_expI_part (K : ℂ) (hK : ‖K‖ = 1) (N : ℕ) (x : ℝ) :
    |(K * Complex.exp ((x : ℂ) * I)).re - ∑ j ∈ range N, (K * I ^ j / (j.factorial : ℂ)).re * x ^ j| ≤
      |x| ^ N / (N.factorial : ℝ) := by
  rcases N with _ | m
  · simp only [range_zero, sum_empty, sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    calc |(K * Complex.exp ((x : ℂ) * I)).re| ≤ ‖K * Complex.exp ((x : ℂ) * I)‖ := Complex.abs_re_le_norm _
      _ = 1 := by rw [norm_mul, hK, Complex.norm_exp_ofReal_mul_I, one_mul]
  -- the chain T j t = tau K 0 I 0 j t
  set T : ℕ → ℝ → ℝ := fun j t => tau K 0 I 0 j t with hT
  have hchain : ∀ j ≤ m, ∀ t, HasDerivAt (T j) (((j : ℝ) + 1) * T (j + 1) t) t :=
    fun j _ t => hasDerivAt_tau K 0 I 0 j t
  have hTj : ∀ j t, T j t = (K * (Complex.exp ((t : ℂ) * I) * (I ^ j / (j.factorial : ℂ)))).re := by
    intro j t
    simp only [hT, tau, zero_mul, zero_add, mul_zero, add_zero]
    rw [Chk.ecoef_beta_zero, mul_comm I]
  have hM : ∀ t ∈ Set.Icc (0 - |x|) (0 + |x|), |T (m + 1) t| ≤ 1 / ((m + 1).factorial : ℝ) := by
    intro t _
    rw [hTj]
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, hK, one_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_div, norm_pow, Complex.norm_I,
      one_pow, Complex.norm_natCast, one_div]
  have hx : x ∈ Set.Icc (0 - |x|) (0 + |x|) := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have h := taylorK hchain hM x hx
  rw [hTj] at h
  unfold npoly at h
  simp only [sub_zero] at h
  have e1 : ∑ j ∈ range (m + 1), T j 0 * x ^ j = ∑ j ∈ range (m + 1), (K * I ^ j / (j.factorial : ℂ)).re * x ^ j := by
    refine sum_congr rfl (fun j _ => ?_)
    rw [hTj]; simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    congr 2; ring
  rw [e1] at h
  have e2 : (K * (Complex.exp ((x : ℂ) * I) * (I ^ 0 / ((0 : ℕ).factorial : ℂ)))).re =
      (K * Complex.exp ((x : ℂ) * I)).re := by simp
  rw [e2] at h
  calc _ ≤ 1 / ((m + 1).factorial : ℝ) * |x| ^ (m + 1) := h
    _ = |x| ^ (m + 1) / ((m + 1).factorial : ℝ) := by ring

theorem re_I_pow_even (n : ℕ) : (1 * I ^ (2 * n) / (((2 * n).factorial : ℕ) : ℂ)).re = (-1) ^ n / ((2 * n).factorial : ℝ) := by
  rw [one_mul, pow_mul, Complex.I_sq]
  have : ((-1 : ℂ) ^ n / (((2 * n).factorial : ℕ) : ℂ)) = (((-1 : ℝ) ^ n / ((2 * n).factorial : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

theorem re_I_pow_odd (n : ℕ) : (1 * I ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ)).re = 0 := by
  rw [one_mul, pow_succ, pow_mul, Complex.I_sq]
  have : ((-1 : ℂ) ^ n * I / (((2 * n + 1).factorial : ℕ) : ℂ)) =
      (((-1 : ℝ) ^ n / ((2 * n + 1).factorial : ℝ) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul, Complex.I_re, mul_zero]

/-- `|cos x - Σ_{n<N} (-1)^n x^{2n}/(2n)!| ≤ |x|^{2N}/(2N)!` for all real `x`. -/
theorem taylor_cos (N : ℕ) (x : ℝ) :
    |Real.cos x - ∑ n ∈ range N, (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ)| ≤
      |x| ^ (2 * N) / ((2 * N).factorial : ℝ) := by
  have h := taylor_expI_part 1 (by simp) (2 * N) x
  have e1 : (1 * Complex.exp ((x : ℂ) * I)).re = Real.cos x := by
    rw [one_mul, Complex.exp_ofReal_mul_I_re]
  have e2 : ∀ N : ℕ, ∑ j ∈ range (2 * N), (1 * I ^ j / (j.factorial : ℂ)).re * x ^ j =
      ∑ n ∈ range N, (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ,
        re_I_pow_even, re_I_pow_odd]
      ring
  rw [e1, e2] at h; exact h

end SignUnc
