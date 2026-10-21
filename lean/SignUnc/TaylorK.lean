import SignUnc.TaylorN

/-!
# Two-sided Taylor bound for a chain of normalized Taylor coefficients

If `T j` has derivative `(j+1) T (j+1)` for `j ≤ m` and `|T (m+1)| ≤ M` on `[c - η, c + η]`, then
`|T 0 y - Σ_{j ≤ m} T j c (y - c)^j| ≤ M |y - c|^{m+1}` there (`T j = f^{(j)}/j!`).
-/

open Real Finset

namespace SignUnc

/-- The normalized Taylor polynomial `Σ_{j ≤ m} T j c (y - c)^j`. -/
noncomputable def npoly (T : ℕ → ℝ → ℝ) (c : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ range (m + 1), T j c * (y - c) ^ j

/-- The factorial-scaled chain `F j = j! T j` has `F j' = F (j+1)`. -/
theorem chain_of_norm {m : ℕ} {T : ℕ → ℝ → ℝ} (hT : ∀ j ≤ m, ∀ x, HasDerivAt (T j) (((j : ℝ) + 1) * T (j + 1) x) x) :
    ∀ j ≤ m, ∀ x, HasDerivAt (fun x => (j.factorial : ℝ) * T j x) (((j + 1).factorial : ℝ) * T (j + 1) x) x := by
  intro j hj x
  have := (hT j hj x).const_mul (j.factorial : ℝ)
  refine this.congr_deriv ?_
  rw [Nat.factorial_succ]; push_cast; ring

theorem tpoly_of_norm (T : ℕ → ℝ → ℝ) (c : ℝ) (m : ℕ) (y : ℝ) :
    tpoly (fun j x => (j.factorial : ℝ) * T j x) c m y = npoly T c m y := by
  unfold tpoly npoly
  refine sum_congr rfl (fun j _ => ?_)
  have : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  field_simp

/-- Lower bound on the right: `npoly - M (y-c)^{m+1} ≤ T 0 y` on `[c, c + η]`. -/
theorem taylorK_right_lower {m : ℕ} {T : ℕ → ℝ → ℝ}
    (hT : ∀ j ≤ m, ∀ x, HasDerivAt (T j) (((j : ℝ) + 1) * T (j + 1) x) x) {c η M : ℝ}
    (hM : ∀ x ∈ Set.Icc c (c + η), |T (m + 1) x| ≤ M) :
    ∀ y ∈ Set.Icc c (c + η), npoly T c m y - M * (y - c) ^ (m + 1) ≤ T 0 y := by
  intro y hy
  have hF := chain_of_norm hT
  have hMF : ∀ x ∈ Set.Icc c (c + η), |(fun j x => (j.factorial : ℝ) * T j x) (m + 1) x| ≤ ((m + 1).factorial : ℝ) * M := by
    intro x hx
    simp only
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hM x hx) (by positivity)
  have := taylorN_right m (fun j x => (j.factorial : ℝ) * T j x) hF hMF y hy
  rw [tpoly_of_norm] at this
  have hf : ((m + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul] at this
  have e : ((m + 1).factorial : ℝ) * M * ((y - c) ^ (m + 1) / ((m + 1).factorial : ℝ)) = M * (y - c) ^ (m + 1) := by
    field_simp
  linarith [e]

theorem npoly_neg (T : ℕ → ℝ → ℝ) (c : ℝ) (m : ℕ) (y : ℝ) :
    npoly (fun j x => -T j x) c m y = -npoly T c m y := by
  unfold npoly; rw [← sum_neg_distrib]; refine sum_congr rfl (fun j _ => ?_); ring

/-- Two-sided bound on the right half `[c, c + η]`. -/
theorem taylorK_right {m : ℕ} {T : ℕ → ℝ → ℝ}
    (hT : ∀ j ≤ m, ∀ x, HasDerivAt (T j) (((j : ℝ) + 1) * T (j + 1) x) x) {c η M : ℝ}
    (hM : ∀ x ∈ Set.Icc c (c + η), |T (m + 1) x| ≤ M) :
    ∀ y ∈ Set.Icc c (c + η), |T 0 y - npoly T c m y| ≤ M * |y - c| ^ (m + 1) := by
  intro y hy
  have h1 := taylorK_right_lower hT hM y hy
  have hTn : ∀ j ≤ m, ∀ x, HasDerivAt (fun x => -T j x) (((j : ℝ) + 1) * (fun x => -T (j + 1) x) x) x := by
    intro j hj x
    have := (hT j hj x).neg
    refine this.congr_deriv ?_; simp only; ring
  have hMn : ∀ x ∈ Set.Icc c (c + η), |(fun x => -T (m + 1) x) x| ≤ M := by
    intro x hx; simp only [abs_neg]; exact hM x hx
  have h2 := taylorK_right_lower (T := fun j x => -T j x) hTn hMn y hy
  rw [npoly_neg] at h2
  have hyc : 0 ≤ y - c := by linarith [hy.1]
  rw [abs_of_nonneg hyc]
  rw [abs_le]
  constructor <;> linarith

/-- The reflected chain `S j x = (-1)^j T j (2c - x)`. -/
theorem chain_reflect {m : ℕ} {T : ℕ → ℝ → ℝ}
    (hT : ∀ j ≤ m, ∀ x, HasDerivAt (T j) (((j : ℝ) + 1) * T (j + 1) x) x) (c : ℝ) :
    ∀ j ≤ m, ∀ x, HasDerivAt (fun x => (-1) ^ j * T j (2 * c - x))
      (((j : ℝ) + 1) * ((-1) ^ (j + 1) * T (j + 1) (2 * c - x))) x := by
  intro j hj x
  have hin : HasDerivAt (fun x : ℝ => 2 * c - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (2 * c)
  have := ((hT j hj (2 * c - x)).comp x hin).const_mul ((-1) ^ j)
  refine this.congr_deriv ?_
  rw [pow_succ]; ring

theorem npoly_reflect (T : ℕ → ℝ → ℝ) (c : ℝ) (m : ℕ) (y : ℝ) :
    npoly (fun j x => (-1) ^ j * T j (2 * c - x)) c m (2 * c - y) = npoly T c m y := by
  unfold npoly
  refine sum_congr rfl (fun j _ => ?_)
  simp only
  rw [show 2 * c - c = c by ring, show 2 * c - y - c = (-1) * (y - c) by ring, mul_pow]
  have h : ((-1 : ℝ) ^ j) * ((-1) ^ j) = 1 := by rw [← mul_pow]; norm_num
  calc (-1) ^ j * T j c * ((-1) ^ j * (y - c) ^ j) = T j c * (y - c) ^ j * ((-1) ^ j * (-1) ^ j) := by ring
    _ = T j c * (y - c) ^ j := by rw [h, mul_one]

/-- Two-sided Taylor bound on `[c - η, c + η]`. -/
theorem taylorK {m : ℕ} {T : ℕ → ℝ → ℝ}
    (hT : ∀ j ≤ m, ∀ x, HasDerivAt (T j) (((j : ℝ) + 1) * T (j + 1) x) x) {c η M : ℝ}
    (hM : ∀ x ∈ Set.Icc (c - η) (c + η), |T (m + 1) x| ≤ M) :
    ∀ y ∈ Set.Icc (c - η) (c + η), |T 0 y - npoly T c m y| ≤ M * |y - c| ^ (m + 1) := by
  intro y hy
  rcases le_total c y with hcy | hyc
  · exact taylorK_right hT (fun x hx => hM x ⟨by linarith [hx.1, hy.1, hy.2], hx.2⟩) y ⟨hcy, hy.2⟩
  · -- reflect: y' = 2c - y ∈ [c, c + η]
    have hS := chain_reflect hT c
    have hMS : ∀ x ∈ Set.Icc c (c + η), |(fun x => (-1) ^ (m + 1) * T (m + 1) (2 * c - x)) x| ≤ M := by
      intro x hx
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hM _ ⟨by linarith [hx.2], by linarith [hx.1, hy.1, hy.2]⟩
    have h := taylorK_right (T := fun j x => (-1) ^ j * T j (2 * c - x)) hS hMS (2 * c - y)
      ⟨by linarith, by linarith [hy.1]⟩
    rw [npoly_reflect] at h
    simp only [pow_zero, one_mul, show 2 * c - (2 * c - y) = y by ring] at h
    rwa [show 2 * c - y - c = -(y - c) by ring, abs_neg] at h

end SignUnc
