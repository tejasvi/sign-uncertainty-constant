import SignUnc.LowSound2
import SignUnc.Lower.Kappa

/-!
# Soundness of the lower checker, part 3: `φ̂` against `P̂`

`φ₀ = 1 - v + ψ` (smooth), `P̂(y) = Σ_k 2 ∫_{lo_k}^{hi_k} P_k(t) cos(2πyt) dt` over the chain of pieces of `[0, r]`.
If `|φ₀ - P_k| ≤ ε` on every piece, then `|φ̂ - P̂| ≤ 2rε`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex Finset MeasureTheory intervalIntegral

variable {P : ℕ}

/-- The left end of a piece in `ℝ`. -/
noncomputable def plo (pc : PPiece) : ℝ := ((pc.1 : ℕ) : ℝ) / 10000
/-- The right end of a piece in `ℝ`. -/
noncomputable def phi' (pc : PPiece) : ℝ := ((pc.2.1 : ℕ) : ℝ) / 10000

/-- `P̂(y) = Σ_k 2 ∫_{lo_k}^{hi_k} P_k(t) cos(2πyt) dt`. -/
noncomputable def PhatS (P : ℕ) (ps : List PPiece) (y : ℝ) : ℝ :=
  (ps.map fun pc => 2 * ∫ t in plo pc..phi' pc, Peval P pc t * Real.cos (2 * π * y * t)).sum

theorem continuous_Peval (pc : PPiece) : Continuous (Peval P pc) := by
  unfold Peval; fun_prop

/-- Additivity over a chain of pieces. -/
theorem integral_chain {f : ℝ → ℝ} (hf : Continuous f) :
    ∀ (a : ℕ) (ps : List PPiece), chainOK a ps = true →
      ∫ t in ((a : ℕ) : ℝ) / 10000..(5502 : ℝ) / 10000, f t = (ps.map fun pc => ∫ t in plo pc..phi' pc, f t).sum
  | a, [], h => by
    simp only [chainOK, decide_eq_true_eq] at h
    subst h; simp
  | a, pc :: L, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.map_cons, List.sum_cons, ← integral_chain hf pc.2.1 L h2,
      ← integral_add_adjacent_intervals (b := phi' pc) (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    rw [plo, h1]
    rfl

namespace LCertP

variable {C : LCert}

/-- `φ̂(y) = 2 ∫_0^r (1 - v + ψ) cos(2πy·)`. -/
theorem phihat_eq (h : C.Ok) (y : ℝ) :
    C.phihat y = 2 * ∫ t in (0 : ℝ)..C.r, (1 - C.v t + C.psi t) * Real.cos (2 * π * y * t) := by
  have hr := h.hr
  set f : ℝ → ℝ := fun t => (1 - C.v t + C.psi t) * Real.cos (2 * π * y * t) with hfdef
  have hfc : Continuous f := ((continuous_const.sub LCert.continuous_v).add h.hψc).mul (by fun_prop)
  have hfe : ∀ t, f (-t) = f t := fun t => by
    simp only [hfdef, LCert.v_neg, h.hψe, show 2 * π * y * -t = -(2 * π * y * t) by ring, Real.cos_neg]
  unfold LCert.phihat cosT LCert.phi
  have e1 : (fun t => (Set.Icc (-C.r) C.r).indicator (fun x => 1 - C.v x + C.psi x) t * Real.cos (2 * π * y * t)) =
      (Set.Icc (-C.r) C.r).indicator f := by
    funext t; by_cases ht : t ∈ Set.Icc (-C.r) C.r
    · simp [Set.indicator_of_mem ht, hfdef]
    · simp [Set.indicator_of_notMem ht]
  rw [e1, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc, ← integral_of_le (by linarith),
    ← integral_add_adjacent_intervals (b := 0) (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
  have e2 : ∫ t in -C.r..0, f t = ∫ t in (0 : ℝ)..C.r, f t := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := C.r) f
    simp only [neg_zero] at h1
    rw [← h1]
    congr 1; funext t; exact hfe t
  rw [e2]; ring

end LCertP

theorem abs_listSum_sub_le {α : Type*} (f g : α → ℝ) :
    ∀ L : List α, |(L.map f).sum - (L.map g).sum| ≤ (L.map fun x => |f x - g x|).sum
  | [] => by simp
  | x :: L => by
    simp only [List.map_cons, List.sum_cons]
    have := abs_listSum_sub_le f g L
    calc |f x + (L.map f).sum - (g x + (L.map g).sum)| = |(f x - g x) + ((L.map f).sum - (L.map g).sum)| := by
          ring_nf
      _ ≤ |f x - g x| + |(L.map f).sum - (L.map g).sum| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem listSum_le_listSum {α : Type*} {f g : α → ℝ} :
    ∀ (L : List α), (∀ x ∈ L, f x ≤ g x) → (L.map f).sum ≤ (L.map g).sum
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (listSum_le_listSum L (fun y hy => h y (by simp [hy])))

/-- `|φ̂ - P̂| ≤ 2rε` from `|φ₀ - P_k| ≤ ε` on every piece of a chain covering `[0, r]`. -/
theorem phihat_PhatS {C : LCert} (h : C.Ok) (hr : C.r = 5502 / 10000) {ps : List PPiece} (hch : chainOK 0 ps = true)
    (hord : ∀ pc ∈ ps, pc.1 ≤ pc.2.1)
    {ε : ℝ} (hε : ∀ pc ∈ ps, ∀ t ∈ Set.Icc (plo pc) (phi' pc), |1 - C.v t + C.psi t - Peval P pc t| ≤ ε) (y : ℝ) :
    |C.phihat y - PhatS P ps y| ≤ 2 * C.r * ε := by
  set φ0 : ℝ → ℝ := fun t => 1 - C.v t + C.psi t with hφ0
  have hφc : Continuous φ0 := (continuous_const.sub LCert.continuous_v).add h.hψc
  have hchain := integral_chain (f := fun t => φ0 t * Real.cos (2 * π * y * t)) (hφc.mul (by fun_prop)) 0 ps hch
  have hlen := integral_chain (f := fun _ => (1 : ℝ)) continuous_const 0 ps hch
  simp only [Nat.cast_zero, zero_div, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hlen hchain
  rw [LCertP.phihat_eq h y, show C.r = (5502 : ℝ) / 10000 from hr, hchain, PhatS, ← List.sum_map_mul_left]
  have hpiece : ∀ pc ∈ ps, |2 * (∫ t in plo pc..phi' pc, φ0 t * Real.cos (2 * π * y * t)) -
      2 * ∫ t in plo pc..phi' pc, Peval P pc t * Real.cos (2 * π * y * t)| ≤ 2 * ε * (phi' pc - plo pc) := by
    intro pc hpc
    have hle : plo pc ≤ phi' pc := by
      unfold plo phi'; have := hord pc hpc; gcongr
    have hsub : (∫ t in plo pc..phi' pc, φ0 t * Real.cos (2 * π * y * t)) -
        ∫ t in plo pc..phi' pc, Peval P pc t * Real.cos (2 * π * y * t) =
        ∫ t in plo pc..phi' pc, (φ0 t * Real.cos (2 * π * y * t) - Peval P pc t * Real.cos (2 * π * y * t)) :=
      (intervalIntegral.integral_sub (f := fun t => φ0 t * Real.cos (2 * π * y * t))
        (g := fun t => Peval P pc t * Real.cos (2 * π * y * t))
        ((hφc.mul (by fun_prop)).intervalIntegrable _ _)
        (((continuous_Peval pc).mul (by fun_prop)).intervalIntegrable _ _)).symm
    rw [← mul_sub, hsub, abs_mul, abs_two]
    have := norm_integral_le_of_norm_le_const (a := plo pc) (b := phi' pc) (C := ε)
      (f := fun t => φ0 t * Real.cos (2 * π * y * t) - Peval P pc t * Real.cos (2 * π * y * t)) (fun t ht => by
        rw [Set.uIoc_of_le hle] at ht
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
        have h1 := hε pc hpc t ⟨ht.1.le, ht.2⟩
        have h2 := Real.abs_cos_le_one (2 * π * y * t)
        calc |φ0 t - Peval P pc t| * |Real.cos (2 * π * y * t)| ≤ ε * 1 :=
              mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
          _ = ε := mul_one _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ phi' pc - plo pc)] at this
    nlinarith [this]
  refine (abs_listSum_sub_le _ _ ps).trans ?_
  refine (listSum_le_listSum ps hpiece).trans (le_of_eq ?_)
  rw [List.sum_map_mul_left, ← hlen]
  ring

end SignUnc.Chk
