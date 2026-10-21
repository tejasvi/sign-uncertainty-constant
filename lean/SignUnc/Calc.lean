import SignUnc.Upper

/-!
# Derivatives of the Gaussian pairs and a second-order lower bound

`gb1, gb2` and `gbh1, gbh2` are the first and second derivatives of `gb` and `gbh` (proved with `HasDerivAt`);
`gsum1, gsum2` those of `gsum`.  `taylor2_lower`: if `|f''| ≤ M` on `[y₀ - e, y₀ + e]`, then
`f y ≥ f y₀ - |f'(y₀)| e - M e²/2` there.
-/

open Real

namespace SignUnc

/-- `gb'`. -/
noncomputable def gb1 (a s y : ℝ) : ℝ :=
  -(2 * π * a) * ((y - s) * Real.exp (-π * a * (y - s) ^ 2) + (y + s) * Real.exp (-π * a * (y + s) ^ 2))

/-- `gb''`. -/
noncomputable def gb2 (a s y : ℝ) : ℝ :=
  (4 * (π * a) ^ 2 * (y - s) ^ 2 - 2 * (π * a)) * Real.exp (-π * a * (y - s) ^ 2) +
    (4 * (π * a) ^ 2 * (y + s) ^ 2 - 2 * (π * a)) * Real.exp (-π * a * (y + s) ^ 2)

/-- `gbh'`. -/
noncomputable def gbh1 (a s y : ℝ) : ℝ :=
  2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
    (-(2 * (π * y / a)) * Real.cos (2 * π * s * y) - 2 * (π * s) * Real.sin (2 * π * s * y))

/-- `gbh''`. -/
noncomputable def gbh2 (a s y : ℝ) : ℝ :=
  2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
    ((4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2) * Real.cos (2 * π * s * y) +
      8 * (π * s) * (π * y / a) * Real.sin (2 * π * s * y))

theorem hasDerivAt_gauss (a s y : ℝ) :
    HasDerivAt (fun y => Real.exp (-π * a * (y - s) ^ 2))
      (-(2 * π * a) * (y - s) * Real.exp (-π * a * (y - s) ^ 2)) y := by
  have h := (((hasDerivAt_id y).sub_const s).pow 2).const_mul (-π * a)
  have h2 := h.exp
  refine h2.congr_deriv ?_
  simp; ring

theorem hasDerivAt_gb (a s y : ℝ) : HasDerivAt (gb a s) (gb1 a s y) y := by
  have h1 := hasDerivAt_gauss a s y
  have h2 := hasDerivAt_gauss a (-s) y
  simp only [sub_neg_eq_add] at h2
  have := h1.add h2
  unfold gb gb1
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_gb1 (a s y : ℝ) : HasDerivAt (gb1 a s) (gb2 a s y) y := by
  have h1 := ((hasDerivAt_id y).sub_const s).mul (hasDerivAt_gauss a s y)
  have h2 := ((hasDerivAt_id y).add_const s).mul (hasDerivAt_gauss a (-s) y)
  simp only [sub_neg_eq_add] at h2
  have := (h1.add h2).const_mul (-(2 * π * a))
  unfold gb1 gb2
  refine this.congr_deriv ?_
  simp; ring

theorem hasDerivAt_H (a y : ℝ) :
    HasDerivAt (fun y => Real.exp (-π * y ^ 2 / a)) (-(2 * (π * y / a)) * Real.exp (-π * y ^ 2 / a)) y := by
  have h := (((hasDerivAt_id y).pow 2).const_mul (-π)).div_const a
  have h2 := h.exp
  refine h2.congr_deriv ?_
  simp; ring

theorem hasDerivAt_cos2 (s y : ℝ) :
    HasDerivAt (fun y => Real.cos (2 * π * s * y)) (-(2 * (π * s)) * Real.sin (2 * π * s * y)) y := by
  have h := ((hasDerivAt_id y).const_mul (2 * π * s)).cos
  refine h.congr_deriv ?_
  simp; ring

theorem hasDerivAt_sin2 (s y : ℝ) :
    HasDerivAt (fun y => Real.sin (2 * π * s * y)) (2 * (π * s) * Real.cos (2 * π * s * y)) y := by
  have h := ((hasDerivAt_id y).const_mul (2 * π * s)).sin
  refine h.congr_deriv ?_
  simp; ring

theorem hasDerivAt_gbh (a s y : ℝ) : HasDerivAt (gbh a s) (gbh1 a s y) y := by
  have h := ((hasDerivAt_H a y).mul (hasDerivAt_cos2 s y)).const_mul (2 / Real.sqrt a)
  unfold gbh gbh1
  have e : (fun y => 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * Real.cos (2 * π * s * y)) =
      fun y => 2 / Real.sqrt a * (Real.exp (-π * y ^ 2 / a) * Real.cos (2 * π * s * y)) := by
    ext y; ring
  rw [e]
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_gbh1 (a s y : ℝ) (ha : a ≠ 0) : HasDerivAt (gbh1 a s) (gbh2 a s y) y := by
  have hin : HasDerivAt (fun y => -(2 * (π * y / a)) * Real.cos (2 * π * s * y) -
      2 * (π * s) * Real.sin (2 * π * s * y))
      (-(2 * (π / a)) * Real.cos (2 * π * s * y) +
        -(2 * (π * y / a)) * (-(2 * (π * s)) * Real.sin (2 * π * s * y)) -
        2 * (π * s) * (2 * (π * s) * Real.cos (2 * π * s * y))) y := by
    have h1 : HasDerivAt (fun y => -(2 * (π * y / a))) (-(2 * (π / a))) y := by
      have := (((hasDerivAt_id y).const_mul π).div_const a).const_mul 2 |>.neg
      refine this.congr_deriv ?_; simp
    have := (h1.mul (hasDerivAt_cos2 s y)).sub ((hasDerivAt_sin2 s y).const_mul (2 * (π * s)))
    refine this.congr_deriv ?_
    ring
  have h := ((hasDerivAt_H a y).mul hin).const_mul (2 / Real.sqrt a)
  unfold gbh1 gbh2
  have e : (fun y => 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
      (-(2 * (π * y / a)) * Real.cos (2 * π * s * y) - 2 * (π * s) * Real.sin (2 * π * s * y))) =
      fun y => 2 / Real.sqrt a * (Real.exp (-π * y ^ 2 / a) *
      (-(2 * (π * y / a)) * Real.cos (2 * π * s * y) - 2 * (π * s) * Real.sin (2 * π * s * y))) := by
    ext y; ring
  rw [e]
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `Σ c (gb' + gbh')`. -/
noncomputable def gsum1 : List (ℝ × ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (a, s, c) :: L, x => c * (gb1 a s x + gbh1 a s x) + gsum1 L x

/-- `Σ c (gb'' + gbh'')`. -/
noncomputable def gsum2 : List (ℝ × ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (a, s, c) :: L, x => c * (gb2 a s x + gbh2 a s x) + gsum2 L x

theorem hasDerivAt_gsum (L : List (ℝ × ℝ × ℝ)) (y : ℝ) : HasDerivAt (gsum L) (gsum1 L y) y := by
  induction L with
  | nil => simpa [gsum, gsum1] using hasDerivAt_const y (0 : ℝ)
  | cons p L ih =>
    obtain ⟨a, s, c⟩ := p
    have h := (((hasDerivAt_gb a s y).add (hasDerivAt_gbh a s y)).const_mul c).add ih
    have e : gsum ((a, s, c) :: L) = fun x => c * (gb a s x + gbh a s x) + gsum L x := by
      ext x; simp [gsum]
    rw [e]
    exact h.congr_deriv (by simp only [gsum1])

theorem hasDerivAt_gsum1 (L : List (ℝ × ℝ × ℝ)) (hL : ∀ p ∈ L, 0 < p.1) (y : ℝ) :
    HasDerivAt (gsum1 L) (gsum2 L y) y := by
  induction L with
  | nil => simpa [gsum1, gsum2] using hasDerivAt_const y (0 : ℝ)
  | cons p L ih =>
    obtain ⟨a, s, c⟩ := p
    have ha : a ≠ 0 := (hL (a, s, c) (by simp)).ne'
    have h := (((hasDerivAt_gb1 a s y).add (hasDerivAt_gbh1 a s y ha)).const_mul c).add
      (ih (fun q hq => hL q (by simp [hq])))
    have e : gsum1 ((a, s, c) :: L) = fun x => c * (gb1 a s x + gbh1 a s x) + gsum1 L x := by
      ext x; simp [gsum1]
    rw [e]
    exact h.congr_deriv (by simp only [gsum2])

/-- Second-order lower bound. -/
theorem taylor2_lower {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) {y₀ e M : ℝ} (he : 0 ≤ e)
    (hM : ∀ x ∈ Set.Icc (y₀ - e) (y₀ + e), |f2 x| ≤ M) :
    ∀ y ∈ Set.Icc (y₀ - e) (y₀ + e), f y₀ - |f1 y₀| * e - M * e ^ 2 / 2 ≤ f y := by
  intro y hy
  set h : ℝ → ℝ := fun x => f x - f y₀ - f1 y₀ * (x - y₀) + M * (x - y₀) ^ 2 / 2 with hh
  set h1 : ℝ → ℝ := fun x => f1 x - f1 y₀ + M * (x - y₀) with hh1
  have hd : ∀ x, HasDerivAt h (h1 x) x := by
    intro x
    have := ((((hf x).sub_const (f y₀)).sub (((hasDerivAt_id x).sub_const y₀).const_mul (f1 y₀))).add
      ((((hasDerivAt_id x).sub_const y₀).pow 2).const_mul M |>.div_const 2))
    refine this.congr_deriv ?_
    simp [hh1]; ring
  have hd1 : ∀ x, HasDerivAt h1 (f2 x + M) x := by
    intro x
    have := (((hf1 x).sub_const (f1 y₀)).add (((hasDerivAt_id x).sub_const y₀).const_mul M))
    refine this.congr_deriv ?_
    simp
  set D := Set.Icc (y₀ - e) (y₀ + e)
  have hconv : Convex ℝ D := convex_Icc _ _
  have hmono1 : MonotoneOn h1 D := by
    apply monotoneOn_of_deriv_nonneg hconv
    · exact fun x _ => (hd1 x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd1 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd1 x).deriv]
      have := hM x (interior_subset hx)
      linarith [neg_abs_le (f2 x)]
  have h10 : h1 y₀ = 0 := by simp [hh1]
  have hy0 : y₀ ∈ D := ⟨by linarith, by linarith⟩
  have hnn : 0 ≤ h y := by
    rcases le_total y₀ y with hle | hle
    · -- monotone on [y₀, y]
      have hsub : Set.Icc y₀ y ⊆ D := fun x hx => ⟨by linarith [hx.1, hy0.1], by linarith [hx.2, hy.2]⟩
      have hm : MonotoneOn h (Set.Icc y₀ y) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        · exact fun x _ => (hd x).continuousAt.continuousWithinAt
        · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hd x).deriv, ← h10]
          exact hmono1 hy0 (hsub ⟨hx.1.le, hx.2.le⟩) hx.1.le
      have := hm ⟨le_refl _, hle⟩ ⟨hle, le_refl _⟩ hle
      simpa [hh] using this
    · -- antitone on [y, y₀]
      have hsub : Set.Icc y y₀ ⊆ D := fun x hx => ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy0.2]⟩
      have hm : AntitoneOn h (Set.Icc y y₀) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · exact fun x _ => (hd x).continuousAt.continuousWithinAt
        · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hd x).deriv, ← h10]
          exact hmono1 (hsub ⟨hx.1.le, hx.2.le⟩) hy0 hx.2.le
      have := hm ⟨le_refl _, hle⟩ ⟨hle, le_refl _⟩ hle
      simpa [hh] using this
  simp only [hh] at hnn
  have habs : |y - y₀| ≤ e := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h1' : f1 y₀ * (y - y₀) ≥ -(|f1 y₀| * e) := by
    have := abs_mul (f1 y₀) (y - y₀)
    have h3 : |f1 y₀ * (y - y₀)| ≤ |f1 y₀| * e := by
      rw [this]; exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    linarith [neg_abs_le (f1 y₀ * (y - y₀))]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y₀ hy0)
  have h2' : M * (y - y₀) ^ 2 / 2 ≤ M * e ^ 2 / 2 := by
    have : (y - y₀) ^ 2 ≤ e ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have := mul_le_mul_of_nonneg_left this hM0
    linarith
  linarith

/-- One-sided second-order lower bound with the signed first derivative: if `|f''| ≤ M` on `[y₀, y₀ + e]`,
then `f y ≥ f y₀ + f'(y₀) (y - y₀) - M (y - y₀)²/2` there. -/
theorem taylor2_lower_right {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) {y₀ e M : ℝ}
    (hM : ∀ x ∈ Set.Icc y₀ (y₀ + e), |f2 x| ≤ M) :
    ∀ y ∈ Set.Icc y₀ (y₀ + e), f y₀ + f1 y₀ * (y - y₀) - M * (y - y₀) ^ 2 / 2 ≤ f y := by
  intro y hy
  set h : ℝ → ℝ := fun x => f x - f y₀ - f1 y₀ * (x - y₀) + M * (x - y₀) ^ 2 / 2 with hh
  set h1 : ℝ → ℝ := fun x => f1 x - f1 y₀ + M * (x - y₀) with hh1
  have hd : ∀ x, HasDerivAt h (h1 x) x := by
    intro x
    have := ((((hf x).sub_const (f y₀)).sub (((hasDerivAt_id x).sub_const y₀).const_mul (f1 y₀))).add
      ((((hasDerivAt_id x).sub_const y₀).pow 2).const_mul M |>.div_const 2))
    refine this.congr_deriv ?_
    simp [hh1]; ring
  have hd1 : ∀ x, HasDerivAt h1 (f2 x + M) x := by
    intro x
    have := (((hf1 x).sub_const (f1 y₀)).add (((hasDerivAt_id x).sub_const y₀).const_mul M))
    refine this.congr_deriv ?_
    simp
  set D := Set.Icc y₀ (y₀ + e)
  have hmono1 : MonotoneOn h1 D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd1 x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd1 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd1 x).deriv]
      have := hM x (interior_subset hx)
      linarith [neg_abs_le (f2 x)]
  have h10 : h1 y₀ = 0 := by simp [hh1]
  have hy0 : y₀ ∈ D := ⟨le_refl _, le_trans hy.1 hy.2⟩
  have hm : MonotoneOn h D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv, ← h10]
      exact hmono1 hy0 ⟨hx.1.le, hx.2.le⟩ hx.1.le
  have := hm hy0 hy hy.1
  simp only [hh] at this
  simp only [sub_self, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero] at this
  linarith

end SignUnc
