import SignUnc.Calc

/-!
# Third derivatives and a third-order lower bound (for pieces near double zeros of `g`)

`gb3, gbh3` are the derivatives of `gb2, gbh2`; `gsum3` that of `gsum2`.  `taylor3_lower`: if `|f'''| ≤ M` on
`[c - η, c + η]`, then `f x ≥ f c + f'(c) t + f''(c) t²/2 - M |t|³/6` with `t = x - c`.
-/

open Real

namespace SignUnc

/-- `gb'''`. -/
noncomputable def gb3 (a s y : ℝ) : ℝ :=
  (12 * (π * a) ^ 2 * (y - s) - 8 * (π * a) ^ 3 * (y - s) ^ 3) * Real.exp (-π * a * (y - s) ^ 2) +
    (12 * (π * a) ^ 2 * (y + s) - 8 * (π * a) ^ 3 * (y + s) ^ 3) * Real.exp (-π * a * (y + s) ^ 2)

/-- `gbh'''` with `K₁ = 4(πy/a)² - 2π/a - 4(πs)²`, `K₂ = 8(πs)(πy/a)`. -/
noncomputable def gbh3 (a s y : ℝ) : ℝ :=
  2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
    ((-(2 * (π * y / a)) * (4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2) +
        8 * (π / a) * (π * y / a) + 2 * (π * s) * (8 * (π * s) * (π * y / a))) * Real.cos (2 * π * s * y) +
      (-(2 * (π * y / a)) * (8 * (π * s) * (π * y / a)) -
        2 * (π * s) * (4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2) +
        8 * (π * s) * (π / a)) * Real.sin (2 * π * s * y))

theorem hasDerivAt_gb2 (a s y : ℝ) : HasDerivAt (gb2 a s) (gb3 a s y) y := by
  have k1 : HasDerivAt (fun y => 4 * (π * a) ^ 2 * (y - s) ^ 2 - 2 * (π * a))
      (4 * (π * a) ^ 2 * (2 * (y - s))) y := by
    have := ((((hasDerivAt_id y).sub_const s).pow 2).const_mul (4 * (π * a) ^ 2)).sub_const (2 * (π * a))
    refine this.congr_deriv ?_; simp
  have k2 : HasDerivAt (fun y => 4 * (π * a) ^ 2 * (y + s) ^ 2 - 2 * (π * a))
      (4 * (π * a) ^ 2 * (2 * (y + s))) y := by
    have := ((((hasDerivAt_id y).add_const s).pow 2).const_mul (4 * (π * a) ^ 2)).sub_const (2 * (π * a))
    refine this.congr_deriv ?_; simp
  have e2 := hasDerivAt_gauss a (-s) y
  simp only [sub_neg_eq_add] at e2
  have := (k1.mul (hasDerivAt_gauss a s y)).add (k2.mul e2)
  unfold gb2 gb3
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_gbh2 (a s y : ℝ) (ha : a ≠ 0) : HasDerivAt (gbh2 a s) (gbh3 a s y) y := by
  have hK1 : HasDerivAt (fun y => 4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2)
      (8 * (π / a) * (π * y / a)) y := by
    have h0 : HasDerivAt (fun y => π * y / a) (π / a) y := by
      have := ((hasDerivAt_id y).const_mul π).div_const a
      refine this.congr_deriv ?_; simp
    have := (((h0.pow 2).const_mul 4).sub_const (2 * (π / a))).sub_const (4 * (π * s) ^ 2)
    refine this.congr_deriv ?_; simp; ring
  have hK2 : HasDerivAt (fun y => 8 * (π * s) * (π * y / a)) (8 * (π * s) * (π / a)) y := by
    have := (((hasDerivAt_id y).const_mul π).div_const a).const_mul (8 * (π * s))
    refine this.congr_deriv ?_; simp
  have hin : HasDerivAt (fun y => (4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2) * Real.cos (2 * π * s * y) +
      8 * (π * s) * (π * y / a) * Real.sin (2 * π * s * y))
      (8 * (π / a) * (π * y / a) * Real.cos (2 * π * s * y) +
        (4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2) * (-(2 * (π * s)) * Real.sin (2 * π * s * y)) +
        (8 * (π * s) * (π / a) * Real.sin (2 * π * s * y) +
          8 * (π * s) * (π * y / a) * (2 * (π * s) * Real.cos (2 * π * s * y)))) y :=
    (hK1.mul (hasDerivAt_cos2 s y)).add (hK2.mul (hasDerivAt_sin2 s y))
  have h := ((hasDerivAt_H a y).mul hin).const_mul (2 / Real.sqrt a)
  unfold gbh2 gbh3
  have e : (fun y => 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
      ((4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2) * Real.cos (2 * π * s * y) +
        8 * (π * s) * (π * y / a) * Real.sin (2 * π * s * y))) =
      fun y => 2 / Real.sqrt a * (Real.exp (-π * y ^ 2 / a) *
      ((4 * (π * y / a) ^ 2 - 2 * (π / a) - 4 * (π * s) ^ 2) * Real.cos (2 * π * s * y) +
        8 * (π * s) * (π * y / a) * Real.sin (2 * π * s * y))) := by
    ext y; ring
  rw [e]
  refine h.congr_deriv ?_
  ring

/-- `Σ c (gb''' + gbh''')`. -/
noncomputable def gsum3 : List (ℝ × ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (a, s, c) :: L, x => c * (gb3 a s x + gbh3 a s x) + gsum3 L x

theorem hasDerivAt_gsum2 (L : List (ℝ × ℝ × ℝ)) (hL : ∀ p ∈ L, 0 < p.1) (y : ℝ) :
    HasDerivAt (gsum2 L) (gsum3 L y) y := by
  induction L with
  | nil => simpa [gsum2, gsum3] using hasDerivAt_const y (0 : ℝ)
  | cons p L ih =>
    obtain ⟨a, s, c⟩ := p
    have ha : a ≠ 0 := (hL (a, s, c) (by simp)).ne'
    have h := (((hasDerivAt_gb2 a s y).add (hasDerivAt_gbh2 a s y ha)).const_mul c).add
      (ih (fun q hq => hL q (by simp [hq])))
    have e : gsum2 ((a, s, c) :: L) = fun x => c * (gb2 a s x + gbh2 a s x) + gsum2 L x := by
      ext x; simp [gsum2]
    rw [e]
    exact h.congr_deriv (by simp only [gsum3])

/-- Third-order lower bound on `[c, c + η]` (right side). -/
theorem taylor3_right {f f1 f2 f3 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hf2 : ∀ x, HasDerivAt f2 (f3 x) x) {c η M : ℝ}
    (hM : ∀ x ∈ Set.Icc c (c + η), |f3 x| ≤ M) :
    ∀ y ∈ Set.Icc c (c + η), f c + f1 c * (y - c) + f2 c * (y - c) ^ 2 / 2 - M * (y - c) ^ 3 / 6 ≤ f y := by
  intro y hy
  set D := Set.Icc c (c + η)
  set h : ℝ → ℝ := fun x => f x - f c - f1 c * (x - c) - f2 c * (x - c) ^ 2 / 2 + M * (x - c) ^ 3 / 6 with hh
  set h1 : ℝ → ℝ := fun x => f1 x - f1 c - f2 c * (x - c) + M * (x - c) ^ 2 / 2 with hh1
  set h2 : ℝ → ℝ := fun x => f2 x - f2 c + M * (x - c) with hh2
  have hd : ∀ x, HasDerivAt h (h1 x) x := by
    intro x
    have := (((((hf x).sub_const (f c)).sub (((hasDerivAt_id x).sub_const c).const_mul (f1 c))).sub
      ((((hasDerivAt_id x).sub_const c).pow 2).const_mul (f2 c) |>.div_const 2)).add
      ((((hasDerivAt_id x).sub_const c).pow 3).const_mul M |>.div_const 6))
    refine this.congr_deriv ?_
    simp [hh1]; ring
  have hd1 : ∀ x, HasDerivAt h1 (h2 x) x := by
    intro x
    have := ((((hf1 x).sub_const (f1 c)).sub (((hasDerivAt_id x).sub_const c).const_mul (f2 c))).add
      ((((hasDerivAt_id x).sub_const c).pow 2).const_mul M |>.div_const 2))
    refine this.congr_deriv ?_
    simp [hh2]; ring
  have hd2 : ∀ x, HasDerivAt h2 (f3 x + M) x := by
    intro x
    have := (((hf2 x).sub_const (f2 c)).add (((hasDerivAt_id x).sub_const c).const_mul M))
    refine this.congr_deriv ?_
    simp
  have hc : c ∈ D := ⟨le_refl _, le_trans hy.1 hy.2⟩
  have hm2 : MonotoneOn h2 D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd2 x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd2 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd2 x).deriv]
      linarith [neg_abs_le (f3 x), hM x (interior_subset hx)]
  have hm1 : MonotoneOn h1 D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd1 x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd1 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd1 x).deriv, show (0 : ℝ) = h2 c by simp [hh2]]
      exact hm2 hc ⟨hx.1.le, hx.2.le⟩ hx.1.le
  have hm : MonotoneOn h D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv, show (0 : ℝ) = h1 c by simp [hh1]]
      exact hm1 hc ⟨hx.1.le, hx.2.le⟩ hx.1.le
  have := hm hc hy hy.1
  simp only [hh, sub_self] at this
  norm_num at this
  linarith

/-- Third-order lower bound on `[c - η, c]` (left side), from the right side applied to `x ↦ f(2c - x)`. -/
theorem taylor3_left {f f1 f2 f3 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hf2 : ∀ x, HasDerivAt f2 (f3 x) x) {c η M : ℝ}
    (hM : ∀ x ∈ Set.Icc (c - η) c, |f3 x| ≤ M) :
    ∀ y ∈ Set.Icc (c - η) c, f c + f1 c * (y - c) + f2 c * (y - c) ^ 2 / 2 - M * (c - y) ^ 3 / 6 ≤ f y := by
  intro y hy
  -- g(u) = f(2c - u) on [c, c + η]
  have hg : ∀ x, HasDerivAt (fun u => f (2 * c - u)) (-f1 (2 * c - x)) x := by
    intro x
    have := (hf (2 * c - x)).comp x ((hasDerivAt_id x).const_sub (2 * c))
    refine this.congr_deriv ?_; simp
  have hg1 : ∀ x, HasDerivAt (fun u => -f1 (2 * c - u)) (f2 (2 * c - x)) x := by
    intro x
    have := ((hf1 (2 * c - x)).comp x ((hasDerivAt_id x).const_sub (2 * c))).neg
    refine this.congr_deriv ?_; simp
  have hg2 : ∀ x, HasDerivAt (fun u => f2 (2 * c - u)) (-f3 (2 * c - x)) x := by
    intro x
    have := (hf2 (2 * c - x)).comp x ((hasDerivAt_id x).const_sub (2 * c))
    refine this.congr_deriv ?_; simp
  have hM' : ∀ x ∈ Set.Icc c (c + η), |-f3 (2 * c - x)| ≤ M := by
    intro x hx
    rw [abs_neg]; exact hM _ ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have := taylor3_right hg hg1 hg2 hM' (2 * c - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
  simp only [show 2 * c - (2 * c - y) = y by ring, show 2 * c - c = c by ring] at this
  have e1 : -f1 c * (2 * c - y - c) = f1 c * (y - c) := by ring
  have e2 : (2 * c - y - c) ^ 2 = (y - c) ^ 2 := by ring
  have e3 : (2 * c - y - c) ^ 3 = (c - y) ^ 3 := by ring
  rw [e1, e2, e3] at this
  linarith

/-- Third-order lower bound around `c` with the quadratic coefficient: with `κ = f''(c) - M η / 3`,
`f x ≥ f c + f'(c) t + κ t²/2` for `|t| ≤ η`. -/
theorem taylor3_lower {f f1 f2 f3 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hf2 : ∀ x, HasDerivAt f2 (f3 x) x) {c η M : ℝ} (hη : 0 ≤ η)
    (hM : ∀ x ∈ Set.Icc (c - η) (c + η), |f3 x| ≤ M) :
    ∀ y ∈ Set.Icc (c - η) (c + η),
      f c + f1 c * (y - c) + (f2 c - M * η / 3) * (y - c) ^ 2 / 2 ≤ f y := by
  intro y hy
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM c ⟨by linarith, by linarith⟩)
  rcases le_total c y with hcy | hyc
  · have := taylor3_right hf hf1 hf2 (η := η) (fun x hx => hM x ⟨by linarith [hx.1], hx.2⟩) y ⟨hcy, hy.2⟩
    have hb : M * (y - c) ^ 3 / 6 ≤ M * η / 3 * (y - c) ^ 2 / 2 := by
      have h1 : (y - c) ^ 3 ≤ η * (y - c) ^ 2 := by
        have : (y - c) ^ 3 = (y - c) * (y - c) ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right (by linarith [hy.2]) (sq_nonneg _)
      have := mul_le_mul_of_nonneg_left h1 hM0
      nlinarith
    nlinarith
  · have := taylor3_left hf hf1 hf2 (η := η) (fun x hx => hM x ⟨hx.1, by linarith [hx.2]⟩) y ⟨hy.1, hyc⟩
    have hb : M * (c - y) ^ 3 / 6 ≤ M * η / 3 * (y - c) ^ 2 / 2 := by
      have h1 : (c - y) ^ 3 ≤ η * (y - c) ^ 2 := by
        have : (c - y) ^ 3 = (c - y) * (y - c) ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right (by linarith [hy.1]) (sq_nonneg _)
      have := mul_le_mul_of_nonneg_left h1 hM0
      nlinarith
    nlinarith

end SignUnc
