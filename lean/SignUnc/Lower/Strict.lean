import SignUnc.Lower.Dilation

/-!
# Lemma 2.2 with the extremizer: `(S_r)` and `ExtremizerHyp` give `A₊(1)² > r²`
-/

open MeasureTheory Real Set Filter
open scoped ENNReal

namespace SignUnc

theorem Aplus2_gt_of_Sr {r : ℝ} (hr : 0 < r) (hS : Sr r) (hE : ExtremizerHyp) :
    ENNReal.ofReal (r ^ 2) < Aplus2 := by
  obtain ⟨g, hc, hi, he, hft, hg0, hne, hA⟩ := hE
  by_contra hle
  push_neg at hle
  rw [← hA] at hle
  -- `A(g) ≤ r`
  have hAr : A (fun x => (g x : ℂ)) ≤ ENNReal.ofReal r := by
    by_contra hlt
    push_neg at hlt
    have := ENNReal.mul_lt_mul hlt hlt
    rw [← ENNReal.ofReal_mul hr.le, ← sq] at this
    exact absurd hle (not_le.mpr this)
  have hpos : ∀ x, r < |x| → 0 ≤ g x := by
    intro x hx
    have : A (fun x => (g x : ℂ)) < ENNReal.ofReal |x| :=
      lt_of_le_of_lt hAr ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hx)
    simpa using (nonneg_of_A_lt this).2
  exact hne (hS g hc hi he hft hg0.le hpos)

end SignUnc
