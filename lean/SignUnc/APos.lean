import SignUnc.Upper

/-!
# `A(f) > 0` and `A(f̂) > 0` on both classes

Hence the products `A(f) A(f̂)` in `Aplus2` and `C611` never meet the convention `0 · ∞ = 0` of `ℝ≥0∞`:
the infima are those of the paper.
-/

open MeasureTheory Real Complex Set Filter
open scoped FourierTransform ENNReal Topology

namespace SignUnc

/-- `A(f) = 0` forces `f(x)` real and `≥ 0` for every `x ≠ 0`. -/
theorem nonneg_of_A_eq_zero {f : ℝ → ℂ} (h : A f = 0) {x : ℝ} (hx : x ≠ 0) :
    (f x).im = 0 ∧ 0 ≤ (f x).re := by
  have hpos : A f < ENNReal.ofReal |x| := by rw [h]; simpa using abs_pos.mpr hx
  unfold A at hpos
  obtain ⟨r, hr⟩ := iInf_lt_iff.mp hpos
  obtain ⟨hr', hlt⟩ := iInf_lt_iff.mp hr
  have : r < |x| := (ENNReal.ofReal_lt_ofReal_iff (abs_pos.mpr hx)).mp hlt
  exact hr'.2 x this.le

/-- `Re f̂(0) = ∫ f`. -/
theorem ft_zero_re (f : ℝ → ℝ) : (ft f 0).re = ∫ x, f x := by
  unfold ft
  rw [fourier_real_eq]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_complex_ofReal]
  simp

theorem continuous_ft {f : ℝ → ℝ} (hf : Integrable f) : Continuous (ft f) := by
  unfold ft
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hf.ofReal

/-- A set containing `ℝ \ {0}` and closed is everything. -/
theorem closed_compl_zero {S : Set ℝ} (hS : IsClosed S) (h : ({0}ᶜ : Set ℝ) ⊆ S) (x : ℝ) : x ∈ S := by
  have := hS.closure_subset_iff.mpr h
  rw [(dense_compl_singleton (0 : ℝ)).closure_eq] at this
  exact this (mem_univ x)

theorem A_pos_class611 {f : ℝ → ℝ} (hf : Class611 f) : 0 < A (fun x => (f x : ℂ)) := by
  obtain ⟨-, -, -, -, hft0⟩ := hf
  rw [pos_iff_ne_zero]
  intro hA
  have hne0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by rw [ae_iff]; simp
  have hnn : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ f x := by
    filter_upwards [hne0] with x hx
    simpa using (nonneg_of_A_eq_zero hA hx).2
  have := integral_nonneg_of_ae hnn
  rw [ft_zero_re] at hft0
  linarith

theorem A_ft_pos_class611 {f : ℝ → ℝ} (hf : Class611 f) : 0 < A (ft f) := by
  obtain ⟨hint, -, -, -, hft0⟩ := hf
  rw [pos_iff_ne_zero]
  intro hA
  have hc : Continuous (fun ξ => (ft f ξ).re) := Complex.continuous_re.comp (continuous_ft hint)
  have h0 := closed_compl_zero (S := {ξ | 0 ≤ (ft f ξ).re}) (isClosed_le continuous_const hc)
    (fun ξ hξ => by simp only [Set.mem_setOf_eq]; exact (nonneg_of_A_eq_zero hA hξ).2) 0
  simp only [Set.mem_setOf_eq] at h0
  linarith

theorem A_pos_classA {f : ℝ → ℝ} (hf : ClassA f) : 0 < A (fun x => (f x : ℂ)) := by
  obtain ⟨hcont, hint, -, -, -, hft0, hne⟩ := hf
  rw [pos_iff_ne_zero]
  intro hA
  have hall : ∀ x, 0 ≤ f x := fun x => by
    have := closed_compl_zero (S := {x | 0 ≤ f x}) (isClosed_le continuous_const hcont)
      (fun x hx => by simp only [Set.mem_setOf_eq]; simpa using (nonneg_of_A_eq_zero hA hx).2) x
    simpa using this
  have hall' : (0 : ℝ → ℝ) ≤ f := fun x => hall x
  have hint0 : ∫ x, f x = 0 := by
    have : 0 ≤ ∫ x, f x := integral_nonneg hall'
    rw [ft_zero_re] at hft0
    linarith
  have hae : f =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hall' hint).mp hint0
  exact hne ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae)

theorem A_ft_pos_classA {f : ℝ → ℝ} (hf : ClassA f) : 0 < A (ft f) := by
  obtain ⟨hcont, hint, hint', -, h0, -, hne⟩ := hf
  rw [pos_iff_ne_zero]
  intro hA
  have hFc : Continuous (ft f) := continuous_ft hint
  have hre : ∀ ξ, 0 ≤ (ft f ξ).re := fun ξ => by
    have := closed_compl_zero (S := {ξ | 0 ≤ (ft f ξ).re})
      (isClosed_le continuous_const (Complex.continuous_re.comp hFc))
      (fun ξ hξ => by simp only [Set.mem_setOf_eq]; exact (nonneg_of_A_eq_zero hA hξ).2) ξ
    simpa using this
  have him : ∀ ξ, (ft f ξ).im = 0 := fun ξ => by
    have := closed_compl_zero (S := {ξ | (ft f ξ).im = 0})
      (isClosed_eq (Complex.continuous_im.comp hFc) continuous_const)
      (fun ξ hξ => by simp only [Set.mem_setOf_eq]; exact (nonneg_of_A_eq_zero hA hξ).1) ξ
    simpa using this
  have hre' : (0 : ℝ → ℝ) ≤ fun ξ => (ft f ξ).re := fun ξ => hre ξ
  have hinv : 𝓕⁻ (ft f) = fun x => ((f x : ℝ) : ℂ) :=
    Continuous.fourierInv_fourier_eq (Complex.continuous_ofReal.comp hcont) hint.ofReal hint'
  have hf0 : ((f 0 : ℝ) : ℂ) = ∫ ξ, ft f ξ := by
    have := congrFun hinv 0
    rw [← this, fourierInv_eq]
    simp
  have hre0 : f 0 = ∫ ξ, (ft f ξ).re := by
    have := congrArg Complex.re hf0
    rw [Complex.ofReal_re] at this
    rw [this]
    exact (integral_re hint').symm
  have hzero : ∫ ξ, (ft f ξ).re = 0 := le_antisymm (by rw [← hre0]; exact h0) (integral_nonneg hre')
  have hae := (integral_eq_zero_iff_of_nonneg hre' hint'.re).mp hzero
  have hre0' : (fun ξ => (ft f ξ).re) = 0 :=
    (Continuous.ae_eq_iff_eq volume (Complex.continuous_re.comp hFc) continuous_const).mp hae
  have hF0 : ft f = 0 := funext fun ξ => Complex.ext (by simpa using congrFun hre0' ξ) (by simpa using him ξ)
  have hz : (fun x => ((f x : ℝ) : ℂ)) = 0 := by
    rw [← hinv, hF0]; ext x; simp [fourierInv_eq]
  apply hne; ext x; simpa using congrFun hz x

end SignUnc
