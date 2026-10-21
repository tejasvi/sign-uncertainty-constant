import SignUnc.Upper
import SignUnc.APos

/-!
# Refutation probe for the named hypothesis `ExtremizerHyp`

`ExtremizerHyp` (GOS17 Theorem 3 as the paper cites it) is the only named hypothesis of the 6.11 track; it is used
only for the strict lower bound.  The probe shows that no junk value refutes it or makes its last clause degenerate:
1. `probe_clauses`: its first six clauses (continuous, integrable, even, `ĝ = g`, `g 0 = 0`, `g ≠ 0`) hold for an
   explicit Gaussian combination, so they are jointly satisfiable;
2. `probe_le`: every `g` with these six clauses lies in `𝒜`, so `A₊(1)² ≤ A(g)·A(g)`, and `A(g) > 0`; the last clause
   `A(g)·A(g) = A₊(1)²` says exactly that `g` attains the infimum (no `0·⊤` junk: `A(g) > 0`);
3. `probe_bounds`: with the proved bounds, `0 < A₊(1)² < ⊤`, so the last clause forces `0 < A(g) < ⊤`.
-/

open MeasureTheory Real
open scoped ENNReal

namespace SignUnc

/-- `g = (gb 1 0 + gbh 1 0) - (4/3)(gb 4 0 + gbh 4 0) = 4e^{-πx²} - (8/3)e^{-4πx²} - (4/3)e^{-πx²/4}`. -/
noncomputable def probeL : List (ℝ × ℝ × ℝ) := [(1, 0, 1), (4, 0, -(4 / 3))]

theorem probeL_pos : ∀ p ∈ probeL, 0 < p.1 := by
  intro p hp
  simp only [probeL, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> norm_num

theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem probe_g0 : gsum probeL 0 = 0 := by
  simp only [gsum, probeL, gb, gbh, Real.sqrt_one, sqrt_four]
  norm_num

theorem probe_g1 : gsum probeL 1 < 0 := by
  have e : gsum probeL 1 = 4 * Real.exp (-π) - 4 / 3 * (2 * Real.exp (-(4 * π)) + Real.exp (-(π / 4))) := by
    simp only [gsum, probeL, gb, gbh, Real.sqrt_one, sqrt_four, mul_zero, Real.cos_zero, mul_one, sub_zero,
      add_zero, one_pow, zero_add]
    have h1 : -π * 1 * 1 ^ 2 = -π := by ring
    have h2 : -π * 4 * 1 ^ 2 = -(4 * π) := by ring
    have h3 : -π * 1 ^ 2 / 4 = -(π / 4) := by ring
    have h4 : -π * 1 ^ 2 / 1 = -π := by ring
    simp only [one_pow, mul_one, div_one] at *
    rw [show -π * 4 = -(4 * π) by ring, show -π / 4 = -(π / 4) by ring]
    ring
  rw [e]
  have hsplit : Real.exp (-π) = Real.exp (-(π / 4)) * Real.exp (-(3 * π / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : 3 < Real.exp (3 * π / 4) := by
    have := Real.add_one_le_exp (3 * π / 4)
    have hp := Real.pi_gt_three
    linarith
  have h4 : 3 * Real.exp (-(3 * π / 4)) < 1 := by
    rw [Real.exp_neg]
    rw [mul_inv_lt_iff₀ (Real.exp_pos _)]
    linarith
  have h5 : 0 < Real.exp (-(π / 4)) := Real.exp_pos _
  have h6 : 0 < Real.exp (-(4 * π)) := Real.exp_pos _
  rw [hsplit]
  nlinarith

/-- The six clauses of `ExtremizerHyp` other than the extremal one are jointly satisfiable. -/
theorem probe_clauses : ∃ g : ℝ → ℝ, Continuous g ∧ Integrable g ∧ (∀ x, g (-x) = g x) ∧
    ft g = (fun x => (g x : ℂ)) ∧ g 0 = 0 ∧ g ≠ 0 := by
  refine ⟨gsum probeL, continuous_gsum _, integrable_gsum _ probeL_pos, gsum_neg _, ft_gsum _ probeL_pos, probe_g0,
    fun h => ?_⟩
  have := probe_g1
  rw [h] at this
  simp at this

/-- Every `g` with the six clauses lies in `𝒜`: `A₊(1)² ≤ A(g)·A(g)` and `A(g) > 0`. -/
theorem probe_le (g : ℝ → ℝ) (hc : Continuous g) (hi : Integrable g) (he : ∀ x, g (-x) = g x)
    (hft : ft g = fun x => (g x : ℂ)) (h0 : g 0 = 0) (hne : g ≠ 0) :
    Aplus2 ≤ A (fun x => (g x : ℂ)) * A (fun x => (g x : ℂ)) ∧ 0 < A (fun x => (g x : ℂ)) := by
  have hA : ClassA g := by
    refine ⟨hc, hi, ?_, he, h0.le, ?_, hne⟩
    · rw [hft]; exact hi.ofReal
    · rw [hft]; simp [h0]
  refine ⟨?_, A_pos_classA hA⟩
  have := iInf₂_le (f := fun (f : ℝ → ℝ) (_ : ClassA f) => A (fun x => (f x : ℂ)) * A (ft f)) g hA
  rw [hft] at this
  exact this

/-- With the proved bounds, `0 < A₊(1)² < ⊤`. -/
theorem probe_bounds (hlo : LowerStatementWeak) (hup : UpperStatement) : 0 < Aplus2 ∧ Aplus2 < ⊤ := by
  refine ⟨lt_of_lt_of_le ?_ hlo.1, lt_of_le_of_lt hup.1 ENNReal.ofReal_lt_top⟩
  exact ENNReal.ofReal_pos.mpr (by norm_num)

end SignUnc
