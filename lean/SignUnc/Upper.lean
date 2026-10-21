import SignUnc.Gauss

/-!
# The upper bound from an explicit self-dual Gaussian combination (Lemma 5.1 of the paper)

`gsum L = Σ c (gb a s + gbh a s)` over a list `L` of triples `(a, s, c)` with all `a > 0` is even, continuous,
integrable and self-dual.  If `gsum L 0 < 0` and `gsum L ≥ 0` on `[r, ∞)`, then it lies in both classes and
`A(g) = A(ĝ) ≤ r`, so `A₊(1)² ≤ r²` and `C_{6.11} ≤ r²`.
-/

open MeasureTheory Real Complex
open scoped FourierTransform ENNReal

namespace SignUnc

/-- `Σ c (gb a s + gbh a s)` over a list of triples `(a, s, c)`. -/
noncomputable def gsum : List (ℝ × ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (a, s, c) :: L, x => c * (gb a s x + gbh a s x) + gsum L x

theorem gsum_neg (L : List (ℝ × ℝ × ℝ)) (x : ℝ) : gsum L (-x) = gsum L x := by
  induction L with
  | nil => simp [gsum]
  | cons p L ih => obtain ⟨a, s, c⟩ := p; simp [gsum, gb_neg, gbh_neg, ih]

theorem continuous_gsum (L : List (ℝ × ℝ × ℝ)) : Continuous (gsum L) := by
  induction L with
  | nil => simpa [gsum] using continuous_const
  | cons p L ih =>
    obtain ⟨a, s, c⟩ := p
    have : gsum ((a, s, c) :: L) = fun x => c * (gb a s x + gbh a s x) + gsum L x := by
      ext x; simp [gsum]
    rw [this]
    exact (continuous_const.mul ((continuous_gb a s).add (continuous_gbh a s))).add ih

theorem integrable_gsum (L : List (ℝ × ℝ × ℝ)) (hL : ∀ p ∈ L, 0 < p.1) : Integrable (gsum L) := by
  induction L with
  | nil => simpa [gsum] using integrable_zero ℝ ℝ volume
  | cons p L ih =>
    obtain ⟨a, s, c⟩ := p
    have ha : 0 < a := hL (a, s, c) (by simp)
    have : gsum ((a, s, c) :: L) = fun x => c * (gb a s x + gbh a s x) + gsum L x := by
      ext x; simp [gsum]
    rw [this]
    exact (((integrable_gb ha s).add (integrable_gbh ha s)).const_mul c).add
      (ih (fun q hq => hL q (by simp [hq])))

theorem ft_gsum (L : List (ℝ × ℝ × ℝ)) (hL : ∀ p ∈ L, 0 < p.1) :
    ft (gsum L) = fun y => ((gsum L y : ℝ) : ℂ) := by
  induction L with
  | nil =>
    unfold ft; ext y; simp [gsum, fourier_eq]
  | cons p L ih =>
    obtain ⟨a, s, c⟩ := p
    have ha : 0 < a := hL (a, s, c) (by simp)
    have ih' := ih (fun q hq => hL q (by simp [hq]))
    unfold ft at ih' ⊢
    have hsplit : (fun x : ℝ => ((gsum ((a, s, c) :: L) x : ℝ) : ℂ)) = fun x : ℝ =>
        (c : ℂ) * (((gb a s x : ℝ) : ℂ) + ((gbh a s x : ℝ) : ℂ)) + ((gsum L x : ℝ) : ℂ) := by
      ext x; simp only [gsum]; push_cast; ring
    have hi1 : Integrable (fun x : ℝ => (c : ℂ) * (((gb a s x : ℝ) : ℂ) + ((gbh a s x : ℝ) : ℂ))) :=
      ((integrable_gb ha s).ofReal.add (integrable_gbh ha s).ofReal).const_mul _
    have hi2 : Integrable (fun x : ℝ => ((gsum L x : ℝ) : ℂ)) :=
      (integrable_gsum L (fun q hq => hL q (by simp [hq]))).ofReal
    have hadd1 := fourier_add_of_integrable hi1 hi2
    have hi3 : Integrable (fun x : ℝ => ((gb a s x : ℝ) : ℂ)) := (integrable_gb ha s).ofReal
    have hi4 : Integrable (fun x : ℝ => ((gbh a s x : ℝ) : ℂ)) := (integrable_gbh ha s).ofReal
    have hadd2 := fourier_add_of_integrable hi3 hi4
    rw [hsplit, hadd1]
    ext y
    have h1 := congrFun (fourier_const_mul (c : ℂ)
      (fun x : ℝ => ((gb a s x : ℝ) : ℂ) + ((gbh a s x : ℝ) : ℂ))) y
    have h2 := congrFun hadd2 y
    have h3 := congrFun ih' y
    have e1 := congrFun (ft_gb ha s) y
    have e2 := congrFun (ft_gbh ha s) y
    unfold ft at e1 e2
    try simp only at h1 h2 h3 e1 e2 ⊢
    rw [h1, h2, h3, e1, e2]
    ring

/-- `A(g) ≤ r` for an even `g ≥ 0` on `[r, ∞)`. -/
theorem A_le_of_nonneg (g : ℝ → ℝ) (heven : ∀ x, g (-x) = g x) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ y, r ≤ y → 0 ≤ g y) : A (fun x => ((g x : ℝ) : ℂ)) ≤ ENNReal.ofReal r := by
  unfold A
  refine iInf₂_le r ⟨hr, fun x hx => ⟨by simp, ?_⟩⟩
  simp only [Complex.ofReal_re]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx; exact hpos x hx
  · rw [abs_of_neg h] at hx; rw [← heven]; exact hpos (-x) hx

/-- Lemma 5.1 of the paper. -/
theorem upper_of_gsum {r : ℝ} (hr : 0 < r) (L : List (ℝ × ℝ × ℝ)) (hL : ∀ p ∈ L, 0 < p.1)
    (h0 : gsum L 0 < 0) (hpos : ∀ y, r ≤ y → 0 ≤ gsum L y) :
    Aplus2 ≤ ENNReal.ofReal (r ^ 2) ∧ C611 ≤ ENNReal.ofReal (r ^ 2) := by
  set g := gsum L with hg
  have hft : ft g = fun y => ((g y : ℝ) : ℂ) := ft_gsum L hL
  have hA : A (fun x => ((g x : ℝ) : ℂ)) ≤ ENNReal.ofReal r := A_le_of_nonneg g (gsum_neg L) hr hpos
  have hA' : A (ft g) ≤ ENNReal.ofReal r := by rw [hft]; exact hA
  have hprod : A (fun x => ((g x : ℝ) : ℂ)) * A (ft g) ≤ ENNReal.ofReal (r ^ 2) := by
    calc A (fun x => ((g x : ℝ) : ℂ)) * A (ft g) ≤ ENNReal.ofReal r * ENNReal.ofReal r :=
          mul_le_mul' hA hA'
      _ = ENNReal.ofReal (r ^ 2) := by rw [← ENNReal.ofReal_mul hr.le, sq]
  have hft0 : (ft g 0).re = g 0 := by rw [hft]; simp
  constructor
  · have hcl : ClassA g := ⟨continuous_gsum L, integrable_gsum L hL,
      by rw [hft]; exact (integrable_gsum L hL).ofReal, gsum_neg L, h0.le, by rw [hft0]; exact h0.le,
      fun h => by have := congrFun h 0; simp only [Pi.zero_apply] at this; linarith⟩
    exact (iInf₂_le g hcl).trans hprod
  · have hcl : Class611 g := ⟨integrable_gsum L hL, (continuous_gsum L).continuousAt, gsum_neg L, h0,
      by rw [hft0]; exact h0⟩
    exact (iInf₂_le g hcl).trans hprod

end SignUnc
