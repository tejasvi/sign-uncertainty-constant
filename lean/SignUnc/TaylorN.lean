import Mathlib

/-!
# Order-`m` Taylor lower bound from a derivative chain

`F 0 = f`, `HasDerivAt (F j) (F (j+1) x) x` for `j ≤ m`, and `|F (m+1)| ≤ M` on `[c, c + η]` give
`f y ≥ Σ_{j ≤ m} F j c (y - c)^j / j! - M (y - c)^{m+1} / (m+1)!` there.
-/

open Real Finset

namespace SignUnc

/-- The Taylor polynomial `Σ_{j ≤ m} F j c (y - c)^j / j!`. -/
noncomputable def tpoly (F : ℕ → ℝ → ℝ) (c : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ range (m + 1), F j c * ((y - c) ^ j / (j.factorial : ℝ))

theorem hasDerivAt_powfac (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (y - c) ^ (n + 1) / ((n + 1).factorial : ℝ)) ((x - c) ^ n / (n.factorial : ℝ)) x := by
  have := (((hasDerivAt_id x).sub_const c).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
  refine this.congr_deriv ?_
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [id_eq, Nat.add_sub_cancel, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem hasDerivAt_tpoly (F : ℕ → ℝ → ℝ) (c : ℝ) (m : ℕ) (y : ℝ) :
    HasDerivAt (tpoly F c (m + 1)) (tpoly (fun j => F (j + 1)) c m y) y := by
  have he : tpoly F c (m + 1) = fun y =>
      (∑ j ∈ range (m + 1), F (j + 1) c * ((y - c) ^ (j + 1) / ((j + 1).factorial : ℝ))) + F 0 c := by
    funext y; unfold tpoly; rw [sum_range_succ']; simp
  rw [he]
  have h : ∀ j ∈ range (m + 1), HasDerivAt (fun y => F (j + 1) c * ((y - c) ^ (j + 1) / ((j + 1).factorial : ℝ)))
      (F (j + 1) c * ((y - c) ^ j / (j.factorial : ℝ))) y :=
    fun j _ => (hasDerivAt_powfac c j y).const_mul (F (j + 1) c)
  exact ((HasDerivAt.fun_sum h).add_const (F 0 c)).congr_deriv (by unfold tpoly; rfl)

/-- Order-`m` lower bound on `[c, c + η]`. -/
theorem taylorN_right : ∀ (m : ℕ) (F : ℕ → ℝ → ℝ), (∀ j ≤ m, ∀ x, HasDerivAt (F j) (F (j + 1) x) x) →
    ∀ {c η M : ℝ}, (∀ x ∈ Set.Icc c (c + η), |F (m + 1) x| ≤ M) →
      ∀ y ∈ Set.Icc c (c + η), tpoly F c m y - M * ((y - c) ^ (m + 1) / ((m + 1).factorial : ℝ)) ≤ F 0 y := by
  intro m
  induction m with
  | zero =>
    intro F hF c η M hM y hy
    -- h(x) = F 0 x - F 0 c + M (x - c) is monotone
    set h : ℝ → ℝ := fun x => F 0 x - F 0 c + M * (x - c) with hh
    have hd : ∀ x, HasDerivAt h (F 1 x + M) x := by
      intro x
      have := ((hF 0 le_rfl x).sub_const (F 0 c)).add (((hasDerivAt_id x).sub_const c).const_mul M)
      refine this.congr_deriv ?_; simp
    have hc : c ∈ Set.Icc c (c + η) := ⟨le_rfl, le_trans hy.1 hy.2⟩
    have hm : MonotoneOn h (Set.Icc c (c + η)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun x _ => (hd x).continuousAt.continuousWithinAt
      · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hd x).deriv]
        linarith [neg_abs_le (F 1 x), hM x (interior_subset hx)]
    have := hm hc hy hy.1
    simp only [hh, sub_self, mul_zero, add_zero] at this
    simp [tpoly]
    linarith
  | succ m ih =>
    intro F hF c η M hM y hy
    -- the shifted chain bounds the derivative of h(x) = F 0 x - tpoly F c (m+1) x + M (x-c)^{m+2}/(m+2)!
    have hG : ∀ j ≤ m, ∀ x, HasDerivAt ((fun j => F (j + 1)) j) ((fun j => F (j + 1)) (j + 1) x) x :=
      fun j hj x => hF (j + 1) (by omega) x
    have hMG : ∀ x ∈ Set.Icc c (c + η), |(fun j => F (j + 1)) (m + 1) x| ≤ M := fun x hx => hM x hx
    set h : ℝ → ℝ := fun x => F 0 x - tpoly F c (m + 1) x + M * ((x - c) ^ (m + 2) / ((m + 2).factorial : ℝ))
      with hh
    have hd : ∀ x, HasDerivAt h (F 1 x - tpoly (fun j => F (j + 1)) c m x +
        M * ((x - c) ^ (m + 1) / ((m + 1).factorial : ℝ))) x :=
      fun x => ((hF 0 (by omega) x).sub (hasDerivAt_tpoly F c m x)).add
        ((hasDerivAt_powfac c (m + 1) x).const_mul M)
    have hc : c ∈ Set.Icc c (c + η) := ⟨le_rfl, le_trans hy.1 hy.2⟩
    have hm : MonotoneOn h (Set.Icc c (c + η)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun x _ => (hd x).continuousAt.continuousWithinAt
      · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hd x).deriv]
        have hx' : tpoly (fun j => F (j + 1)) c m x - M * ((x - c) ^ (m + 1) / ((m + 1).factorial : ℝ)) ≤ F 1 x :=
          ih (fun j => F (j + 1)) hG hMG x (interior_subset hx)
        linarith
    have h0 : h c = 0 := by
      simp only [hh, tpoly, sub_self]
      rw [sum_range_succ']
      simp
    have key : h c ≤ h y := hm hc hy hy.1
    rw [h0] at key
    have key' : 0 ≤ F 0 y - tpoly F c (m + 1) y + M * ((y - c) ^ (m + 2) / ((m + 2).factorial : ℝ)) := key
    linarith

end SignUnc
