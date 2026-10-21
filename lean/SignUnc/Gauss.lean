import Mathlib
import SignUnc.Defs

/-!
# Gaussian pairs and their Fourier transforms

`gb a s x = e^{-πa(x-s)²} + e^{-πa(x+s)²}` and `gbh a s y = 2 a^{-1/2} e^{-πy²/a} cos(2πsy)` (Definition 3.1
of the paper).  For `a > 0`: `ft (gb a s) = gbh a s` (Mathlib's `fourier_gaussian_pi'`) and
`ft (gbh a s) = gb a s` (Fourier inversion, both functions being even).  A finite combination
`gsum L = Σ c (gb a s + gbh a s)` over a list `L` of triples `(a, s, c)` is therefore self-dual.
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace SignUnc

/-- `e^{-πa(x-s)²} + e^{-πa(x+s)²}`. -/
noncomputable def gb (a s x : ℝ) : ℝ :=
  Real.exp (-π * a * (x - s) ^ 2) + Real.exp (-π * a * (x + s) ^ 2)

/-- `2 a^{-1/2} e^{-πy²/a} cos(2πsy)`. -/
noncomputable def gbh (a s y : ℝ) : ℝ :=
  2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * Real.cos (2 * π * s * y)

theorem continuous_gb (a s : ℝ) : Continuous (gb a s) := by unfold gb; fun_prop

theorem continuous_gbh (a s : ℝ) : Continuous (gbh a s) := by unfold gbh; fun_prop

theorem gb_neg (a s x : ℝ) : gb a s (-x) = gb a s x := by
  unfold gb
  rw [add_comm]; congr 2 <;> ring

theorem gbh_neg (a s y : ℝ) : gbh a s (-y) = gbh a s y := by
  unfold gbh
  rw [show 2 * π * s * -y = -(2 * π * s * y) by ring, Real.cos_neg, neg_sq]

theorem integrable_gauss_shift {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-π * a * (x - s) ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq (b := π * a) (by positivity)).comp_sub_right s
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Function.comp_apply]; ring_nf

theorem integrable_gb {a : ℝ} (ha : 0 < a) (s : ℝ) : Integrable (gb a s) := by
  have h1 := integrable_gauss_shift ha s
  have h2 := integrable_gauss_shift ha (-s)
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [gb, Pi.add_apply, sub_neg_eq_add]

theorem integrable_gbh {a : ℝ} (ha : 0 < a) (s : ℝ) : Integrable (gbh a s) := by
  have h1 : Integrable (fun y : ℝ => Real.exp (-(π / a) * y ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have h2 : Integrable (fun y : ℝ => 2 / Real.sqrt a * Real.exp (-(π / a) * y ^ 2)) := h1.const_mul _
  have h3 := h2.mul_bdd (g := fun y : ℝ => Real.cos (2 * π * s * y)) (c := 1)
    (by fun_prop) (Filter.Eventually.of_forall (fun y => by simpa using Real.abs_cos_le_one _))
  refine h3.congr (Filter.Eventually.of_forall (fun y => ?_))
  simp only [gbh]; ring_nf

/-- Linearity of the Fourier transform on integrable functions. -/
theorem fourier_add_of_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (fun x => f x + g x) = fun t => 𝓕 f t + 𝓕 g t := by
  ext t
  simp only [fourier_eq, smul_add]
  exact integral_add ((fourierIntegral_convergent_iff t).2 hf) ((fourierIntegral_convergent_iff t).2 hg)

theorem fourier_const_mul (K : ℂ) (f : ℝ → ℂ) : 𝓕 (fun x => K * f x) = fun t => K * 𝓕 f t := by
  ext t
  simp only [fourier_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]; congr 1; ext x; ring

/-- The shifted Gaussian: `𝓕 e^{-πa(x-s)²} = a^{-1/2} e^{-πt²/a} e^{-2πist}`. -/
theorem fourier_gauss_shift {a : ℝ} (ha : 0 < a) (s : ℝ) :
    𝓕 (fun x : ℝ => ((Real.exp (-π * a * (x - s) ^ 2) : ℝ) : ℂ)) =
      fun t : ℝ => ((1 / Real.sqrt a * Real.exp (-π * t ^ 2 / a) : ℝ) : ℂ) *
        cexp (-(2 * π * s * t : ℝ) * I) := by
  have h1 : (fun x : ℝ => ((Real.exp (-π * a * (x - s) ^ 2) : ℝ) : ℂ)) = fun x : ℝ =>
      cexp (-π * a * s ^ 2) * cexp (-π * (a : ℂ) * x ^ 2 + 2 * π * ((a * s : ℝ) : ℂ) * x) := by
    ext x; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h1, fourier_const_mul, fourier_gaussian_pi' (b := (a : ℂ)) (by simpa using ha)]
  ext t
  have hsq : (a : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]; push_cast; ring_nf
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs0 : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  rw [hsq]
  push_cast
  have key : -↑π * ↑a * ↑s ^ 2 + -↑π / ↑a * (↑t + I * (↑a * ↑s)) ^ 2
      = -↑π * ↑t ^ 2 / ↑a + -(2 * ↑π * ↑s * ↑t) * I := by
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  calc cexp (-↑π * ↑a * ↑s ^ 2) * (1 / ↑√a * cexp (-↑π / ↑a * (↑t + I * (↑a * ↑s)) ^ 2))
      = 1 / ↑√a * cexp (-↑π * ↑a * ↑s ^ 2 + -↑π / ↑a * (↑t + I * (↑a * ↑s)) ^ 2) := by
        rw [Complex.exp_add]; ring
    _ = 1 / ↑√a * cexp (-↑π * ↑t ^ 2 / ↑a + -(2 * ↑π * ↑s * ↑t) * I) := by rw [key]
    _ = 1 / ↑√a * cexp (-↑π * ↑t ^ 2 / ↑a) * cexp (-(2 * ↑π * ↑s * ↑t) * I) := by
        rw [Complex.exp_add]; ring

theorem two_cos_eq (θ : ℝ) : cexp (-(θ : ℂ) * I) + cexp ((θ : ℂ) * I) = ((2 * Real.cos θ : ℝ) : ℂ) := by
  have h1 : cexp (-(θ : ℂ) * I) = Complex.cos θ - Complex.sin θ * I := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
  rw [h1, Complex.exp_mul_I]
  push_cast
  ring

/-- `𝓕 gb = gbh`. -/
theorem ft_gb {a : ℝ} (ha : 0 < a) (s : ℝ) : ft (gb a s) = fun y => ((gbh a s y : ℝ) : ℂ) := by
  unfold ft
  have hsplit : (fun x : ℝ => ((gb a s x : ℝ) : ℂ)) = fun x : ℝ =>
      ((Real.exp (-π * a * (x - s) ^ 2) : ℝ) : ℂ) + ((Real.exp (-π * a * (x - (-s)) ^ 2) : ℝ) : ℂ) := by
    ext x; simp only [gb, sub_neg_eq_add]; push_cast; ring
  have hadd := fourier_add_of_integrable
    (f := fun x : ℝ => ((Real.exp (-π * a * (x - s) ^ 2) : ℝ) : ℂ))
    (g := fun x : ℝ => ((Real.exp (-π * a * (x - (-s)) ^ 2) : ℝ) : ℂ))
    (integrable_gauss_shift ha s).ofReal (integrable_gauss_shift ha (-s)).ofReal
  rw [hsplit, hadd, fourier_gauss_shift ha, fourier_gauss_shift ha]
  ext y
  rw [← mul_add]
  have e : (-(2 * π * -s * y : ℝ) : ℂ) = ((2 * π * s * y : ℝ) : ℂ) := by push_cast; ring
  rw [e, two_cos_eq]
  simp only [gbh]; push_cast; ring

/-- `𝓕 gbh = gb` (Fourier inversion; both are even). -/
theorem ft_gbh {a : ℝ} (ha : 0 < a) (s : ℝ) : ft (gbh a s) = fun y => ((gb a s y : ℝ) : ℂ) := by
  have hFT : 𝓕 (fun x : ℝ => ((gb a s x : ℝ) : ℂ)) = fun y => ((gbh a s y : ℝ) : ℂ) := ft_gb ha s
  have hinv : 𝓕⁻ (𝓕 (fun x : ℝ => ((gb a s x : ℝ) : ℂ))) = fun x : ℝ => ((gb a s x : ℝ) : ℂ) :=
    Continuous.fourierInv_fourier_eq (Complex.continuous_ofReal.comp (continuous_gb a s))
      (integrable_gb ha s).ofReal (by rw [hFT]; exact (integrable_gbh ha s).ofReal)
  rw [hFT, fourierInv_eq_fourier_comp_neg] at hinv
  simp only [gbh_neg] at hinv
  unfold ft
  exact hinv

end SignUnc
