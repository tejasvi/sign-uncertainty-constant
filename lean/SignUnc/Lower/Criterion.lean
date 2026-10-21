import SignUnc.Lower.Apriori

/-!
# Theorem 3.4: a certificate with (i)-(iv) gives `(S_r)`

The last step of the paper's proof (analytic continuation) is replaced by Lemma 3.3 itself: `P = 0` gives
`‖g‖_{L²(I)} = 0`, so `g` vanishes on `I` too.
-/

open MeasureTheory Real Set Filter

namespace SignUnc

namespace LCert

variable {C : LCert}

theorem phihat_neg (y : ℝ) : C.phihat (-y) = C.phihat y := by
  unfold phihat cosT
  congr 1; funext t; rw [show 2 * π * -y * t = -(2 * π * y * t) by ring, Real.cos_neg]

theorem W_neg (y : ℝ) : C.W (-y) = C.W y := by unfold W; rw [v_neg, phihat_neg]

theorem rho_neg (h : C.Ok) (x : ℝ) : C.rho (-x) = C.rho x := by unfold rho; rw [phihat_neg, h.hψe]

theorem continuous_W (h : C.Ok) : Continuous C.W := (continuous_const.sub continuous_v).add (continuous_phihat h)

theorem continuous_rho (h : C.Ok) : Continuous C.rho := (continuous_phihat h).sub h.hψc

theorem bdd_W (h : C.Ok) : ∃ B, ∀ y, |C.W y| ≤ B := by
  obtain ⟨Bv, hBv⟩ := bdd_v h
  refine ⟨1 + Bv + ∫ t, |C.phi t|, fun y => ?_⟩
  unfold W
  have h1 := hBv y
  have h2 := abs_phihat_le h y
  calc |1 - C.v y + C.phihat y| ≤ |1 - C.v y| + |C.phihat y| := abs_add_le _ _
    _ ≤ (1 + |C.v y|) + |C.phihat y| := by gcongr; exact (abs_sub _ _).trans (by simp)
    _ ≤ 1 + Bv + ∫ t, |C.phi t| := by linarith

/-- Theorem 3.4 of the paper. -/
theorem criterion (h : C.Ok) {m δ κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hK : ∫ x in Icc (-C.r) C.r, (∫ t in Icc (-C.r) C.r, Real.cos (2 * π * x * t) ^ 2) ≤ κ ^ 2)
    (hW : ∀ y, C.r < y → m ≤ C.W y) (hρ : ∀ x ∈ Icc 0 C.r, |C.rho x| ≤ δ)
    (hfin : 2 * C.r * δ < m * (1 - κ)) : Sr C.r := by
  intro g hc hi he hft hg0 hpos
  have hr := h.hr
  set I := Icc (-C.r) C.r with hIdef
  have hcompl : Iᶜ = {y | C.r < |y|} := by
    ext y; simp only [I, mem_compl_iff, mem_Icc, mem_setOf_eq, not_and_or, not_le]
    constructor
    · rintro (hy | hy)
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact hy
    · intro hy
      rcases le_or_gt 0 y with hy0 | hy0
      · right; rwa [abs_of_nonneg hy0] at hy
      · left; rw [abs_of_neg hy0] at hy; linarith
  have hO : ∀ x, x ∉ I → 0 ≤ g x := fun x hx => hpos x (by
    have : x ∈ Iᶜ := hx; rw [hcompl] at this; exact this)
  -- `W ≥ m` on `O`, `|ρ| ≤ δ` on `I`
  have hWO : ∀ y, C.r < |y| → m ≤ C.W y := by
    intro y hy
    rcases le_or_gt 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0] at hy; exact hW y hy
    · rw [abs_of_neg hy0] at hy; rw [← W_neg]; exact hW (-y) hy
  have hρI : ∀ x ∈ I, |C.rho x| ≤ δ := by
    intro x hx
    rcases le_or_gt 0 x with hx0 | hx0
    · exact hρ x ⟨hx0, hx.2⟩
    · rw [← rho_neg h]; exact hρ (-x) ⟨by linarith, by linarith [hx.1]⟩
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hρ 0 ⟨le_rfl, hr.le⟩)
  have hκ' : 0 < 1 - κ := by linarith
  -- `g ≥ 0` on `[r, ∞)` (continuity at `r`)
  have hge : ∀ x, C.r ≤ x → 0 ≤ g x := by
    intro x hx
    have hcl : closure (Ioi C.r) ⊆ {x | 0 ≤ g x} :=
      (isClosed_le continuous_const hc).closure_subset_iff.mpr
        (fun y (hy : C.r < y) => hpos y (by rw [abs_of_pos (by linarith)]; exact hy))
    rw [closure_Ioi] at hcl
    exact hcl hx
  -- the identity
  have hid := identity h hi he hft
  rw [← hIdef] at hid
  set P := ∫ y in Iᶜ, g y with hPdef
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Icc.compl (fun x hx => hO x hx)
  obtain ⟨BW, hBW⟩ := bdd_W h
  have hgW : Integrable (fun y => g y * C.W y) :=
    hi.mul_bdd (continuous_W h).aestronglyMeasurable (Eventually.of_forall fun y => by simpa using hBW y)
  have hWP : m * P ≤ ∫ y in {y | C.r < |y|}, g y * C.W y := by
    rw [← hcompl, hPdef, ← integral_const_mul]
    refine setIntegral_mono_on (hi.const_mul m).integrableOn hgW.integrableOn measurableSet_Icc.compl
      (fun y hy => ?_)
    have hy' : C.r < |y| := by have : y ∈ Iᶜ := hy; rw [hcompl] at this; exact this
    rw [mul_comm m]
    exact mul_le_mul_of_nonneg_left (hWO y hy') (hO y hy)
  have hsum : 0 ≤ (C.coss.map fun q => q.2 * g q.1).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact mul_nonneg (h.hβ q hq).2 (hge q.1 (h.hβ q hq).1)
  -- the residual on `I`
  set N2 := ∫ x in I, g x ^ 2 with hN2def
  have hN20 : 0 ≤ N2 := integral_nonneg (fun x => sq_nonneg _)
  have hIon : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f I := fun hf => hf.continuousOn.integrableOn_Icc
  have hmeas : ∫ x in I, δ ^ 2 = 2 * C.r * δ ^ 2 := by
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, I,
      Real.volume_real_Icc]
    rw [max_eq_left (by linarith)]; ring
  have hres : |∫ x in I, g x * C.rho x| ≤ Real.sqrt N2 * (Real.sqrt (2 * C.r) * δ) := by
    have hcs := sq_integral_mul_le (μ := volume.restrict I) (hIon (hc.pow 2)) (hIon ((continuous_rho h).pow 2))
      (hIon (hc.mul (continuous_rho h)))
    have hρ2 : ∫ x in I, C.rho x ^ 2 ≤ 2 * C.r * δ ^ 2 := by
      rw [← hmeas]
      refine setIntegral_mono_on (hIon ((continuous_rho h).pow 2)) (hIon continuous_const) measurableSet_Icc
        (fun x hx => ?_)
      have := hρI x hx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    apply abs_le_of_sq_le (by positivity)
    rw [← hN2def] at hcs
    calc (∫ x in I, g x * C.rho x) ^ 2 ≤ N2 * ∫ x in I, C.rho x ^ 2 := hcs
      _ ≤ N2 * (2 * C.r * δ ^ 2) := mul_le_mul_of_nonneg_left hρ2 hN20
      _ = (Real.sqrt N2 * (Real.sqrt (2 * C.r) * δ)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hN20, Real.sq_sqrt (by linarith)]
  -- the a priori bound
  have hap := apriori hr hκ1 hκ0 hK hc hi he hft hO
  rw [← hN2def, ← hPdef] at hap
  have h2r : Real.sqrt (2 * C.r) ^ 2 = 2 * C.r := Real.sq_sqrt (by linarith)
  have hsN : 0 ≤ Real.sqrt N2 := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (2 * C.r) := Real.sqrt_nonneg _
  -- `P (m (1-κ) - 2rδ) ≤ 0`, hence `P = 0`
  have hkey : P * (m * (1 - κ) - 2 * C.r * δ) ≤ 0 := by
    have h1 : (1 - κ) * (m * P - Real.sqrt N2 * (Real.sqrt (2 * C.r) * δ)) ≤ 0 := by
      have : m * P - Real.sqrt N2 * (Real.sqrt (2 * C.r) * δ) ≤ g 0 := by
        have := neg_abs_le (∫ x in I, g x * C.rho x)
        linarith
      nlinarith
    have h2 : Real.sqrt N2 * (1 - κ) * (Real.sqrt (2 * C.r) * δ) ≤ Real.sqrt (2 * C.r) * P * (Real.sqrt (2 * C.r) * δ) :=
      mul_le_mul_of_nonneg_right hap (mul_nonneg hs2 hδ0)
    have h3 : Real.sqrt (2 * C.r) * P * (Real.sqrt (2 * C.r) * δ) = 2 * C.r * δ * P := by
      rw [show Real.sqrt (2 * C.r) * P * (Real.sqrt (2 * C.r) * δ) = Real.sqrt (2 * C.r) ^ 2 * P * δ by ring, h2r]
      ring
    have h4 : (1 - κ) * (Real.sqrt N2 * (Real.sqrt (2 * C.r) * δ)) =
        Real.sqrt N2 * (1 - κ) * (Real.sqrt (2 * C.r) * δ) := by ring
    nlinarith
  have hPz : P = 0 := by
    have : 0 < m * (1 - κ) - 2 * C.r * δ := by linarith
    nlinarith
  -- `g = 0` on `O`
  have hgO : EqOn g 0 Iᶜ := by
    have hae : g =ᵐ[volume.restrict Iᶜ] 0 := by
      have := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Icc.compl
        (fun x hx => hO x hx)) hi.integrableOn).mp hPz
      exact this
    exact Measure.eqOn_open_of_ae_eq hae isClosed_Icc.isOpen_compl hc.continuousOn continuousOn_const
  -- `g = 0` on `I`
  have hN2z : N2 = 0 := by
    rw [hPz, mul_zero] at hap
    have : Real.sqrt N2 = 0 := by nlinarith
    have := Real.sqrt_eq_zero'.mp this
    linarith
  have hgI : EqOn g 0 I := by
    have hae2 : (fun x => g x ^ 2) =ᵐ[volume.restrict I] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Icc (fun x _ => sq_nonneg (g x)))
        (hIon (hc.pow 2))).mp hN2z
    have hae : g =ᵐ[volume.restrict I] 0 := by
      filter_upwards [hae2] with x hx
      simpa using hx
    have hsub : I ⊆ closure (interior I) := by
      rw [hIdef, interior_Icc, closure_Ioo (by linarith)]
    exact Measure.eqOn_of_ae_eq hae hc.continuousOn continuousOn_const hsub
  funext x
  by_cases hx : x ∈ I
  · exact hgI hx
  · exact hgO hx

end LCert

end SignUnc
