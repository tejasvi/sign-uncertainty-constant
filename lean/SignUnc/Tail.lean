import SignUnc.Calc

/-!
# The tail `[Y, ∞)` (Program 3 of the paper)

For `y ≥ Y` every Gaussian term is compared with the wide pair's Gaussian `G(y) = e^{-π a_T (y - s_T)²}`:
each exponent minus that of `G` is a quadratic in `y` that does not increase on `[Y, ∞)` (`quad_le`), so
`|gb + gbh|(y) ≤ R · G(y)` with the constant `R = Rpair` evaluated at `Y`.  If
`c_T - c_T R_T - Σ |c_j| R_j > 0`, then `gsum > 0` on `[Y, ∞)`.
-/

open Real

namespace SignUnc

theorem quad_le {a b s t Y y : ℝ} (hab : b ≤ a) (hY : a * s - b * t ≤ (a - b) * Y) (hy : Y ≤ y) :
    -π * a * (y - s) ^ 2 + π * b * (y - t) ^ 2 ≤ -π * a * (Y - s) ^ 2 + π * b * (Y - t) ^ 2 := by
  have key : (-π * a * (y - s) ^ 2 + π * b * (y - t) ^ 2) - (-π * a * (Y - s) ^ 2 + π * b * (Y - t) ^ 2)
      = π * ((y - Y) * (-(a - b) * (y + Y) + 2 * (a * s - b * t))) := by ring
  have h1 : -(a - b) * (y + Y) + 2 * (a * s - b * t) ≤ 0 := by nlinarith
  have h2 : (y - Y) * (-(a - b) * (y + Y) + 2 * (a * s - b * t)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) h1
  have h3 : π * ((y - Y) * (-(a - b) * (y + Y) + 2 * (a * s - b * t))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos pi_pos.le h2
  linarith

/-- The wide pair's Gaussian. -/
noncomputable def Gw (aT sT y : ℝ) : ℝ := Real.exp (-π * aT * (y - sT) ^ 2)

/-- The tail constant of a pair `(a, s)` relative to `(a_T, s_T)` at `Y`. -/
noncomputable def Rpair (aT sT Y a s : ℝ) : ℝ :=
  Real.exp (-π * a * (Y - s) ^ 2 + π * aT * (Y - sT) ^ 2) +
    Real.exp (-π * a * (Y + s) ^ 2 + π * aT * (Y - sT) ^ 2) +
    2 / Real.sqrt a * Real.exp (-π * (1 / a) * (Y - 0) ^ 2 + π * aT * (Y - sT) ^ 2)

/-- The conditions under which `Rpair` bounds the ratio on `[Y, ∞)`. -/
def PairCond (aT sT Y a s : ℝ) : Prop :=
  0 < a ∧ aT ≤ a ∧ a * s - aT * sT ≤ (a - aT) * Y ∧ a * (-s) - aT * sT ≤ (a - aT) * Y ∧
    aT ≤ 1 / a ∧ 1 / a * 0 - aT * sT ≤ (1 / a - aT) * Y

theorem exp_le_mul_Gw {aT sT y q qY e : ℝ} (hq : e = q + π * aT * (y - sT) ^ 2) (hqY : e ≤ qY) :
    Real.exp q ≤ Real.exp qY * Gw aT sT y := by
  unfold Gw
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have : q = e - π * aT * (y - sT) ^ 2 := by linarith
  rw [this]; linarith

theorem abs_pair_le {aT sT Y a s y : ℝ} (h : PairCond aT sT Y a s) (hy : Y ≤ y) :
    |gb a s y + gbh a s y| ≤ Rpair aT sT Y a s * Gw aT sT y := by
  obtain ⟨ha, h1, h2, h3, h4, h5⟩ := h
  have hsq : 0 ≤ 2 / Real.sqrt a := by positivity
  have e1 : Real.exp (-π * a * (y - s) ^ 2) ≤
      Real.exp (-π * a * (Y - s) ^ 2 + π * aT * (Y - sT) ^ 2) * Gw aT sT y :=
    exp_le_mul_Gw rfl (quad_le h1 h2 hy)
  have e2 : Real.exp (-π * a * (y + s) ^ 2) ≤
      Real.exp (-π * a * (Y + s) ^ 2 + π * aT * (Y - sT) ^ 2) * Gw aT sT y := by
    have := exp_le_mul_Gw (aT := aT) (sT := sT) (y := y) (q := -π * a * (y + s) ^ 2)
      (e := -π * a * (y - -s) ^ 2 + π * aT * (y - sT) ^ 2)
      (qY := -π * a * (Y - -s) ^ 2 + π * aT * (Y - sT) ^ 2) (by ring) (quad_le h1 h3 hy)
    simpa only [sub_neg_eq_add] using this
  have e3 : Real.exp (-π * y ^ 2 / a) ≤
      Real.exp (-π * (1 / a) * (Y - 0) ^ 2 + π * aT * (Y - sT) ^ 2) * Gw aT sT y := by
    have := exp_le_mul_Gw (aT := aT) (sT := sT) (y := y) (q := -π * y ^ 2 / a)
      (e := -π * (1 / a) * (y - 0) ^ 2 + π * aT * (y - sT) ^ 2)
      (qY := -π * (1 / a) * (Y - 0) ^ 2 + π * aT * (Y - sT) ^ 2) (by ring) (quad_le h4 h5 hy)
    exact this
  have hcos : |gbh a s y| ≤ 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) := by
    unfold gbh
    rw [abs_mul, abs_mul, abs_of_nonneg hsq, abs_of_pos (Real.exp_pos _)]
    have := Real.abs_cos_le_one (2 * π * s * y)
    have hp : 0 ≤ 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) := by positivity
    nlinarith
  have hgb : |gb a s y| = gb a s y := abs_of_pos (by unfold gb; positivity)
  calc |gb a s y + gbh a s y| ≤ |gb a s y| + |gbh a s y| := abs_add_le _ _
    _ ≤ gb a s y + 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) := by rw [hgb]; linarith
    _ ≤ Rpair aT sT Y a s * Gw aT sT y := by
        unfold gb Rpair
        have := mul_le_mul_of_nonneg_left e3 hsq
        nlinarith

/-- `Σ |c| Rpair` over a list. -/
noncomputable def tailSum (aT sT Y : ℝ) : List (ℝ × ℝ × ℝ) → ℝ
  | [] => 0
  | (a, s, c) :: L => |c| * Rpair aT sT Y a s + tailSum aT sT Y L

theorem gsum_ge_tail {aT sT Y y : ℝ} (hy : Y ≤ y) :
    ∀ L : List (ℝ × ℝ × ℝ), (∀ p ∈ L, PairCond aT sT Y p.1 p.2.1) →
      -(tailSum aT sT Y L * Gw aT sT y) ≤ gsum L y := by
  intro L
  induction L with
  | nil => intro _; simp [tailSum, gsum]
  | cons p L ih =>
    obtain ⟨a, s, c⟩ := p
    intro h
    have hp := abs_pair_le (h (a, s, c) (by simp)) hy
    have hL := ih (fun q hq => h q (by simp [hq]))
    have hc : -(|c| * (Rpair aT sT Y a s * Gw aT sT y)) ≤ c * (gb a s y + gbh a s y) := by
      have h1 : |c * (gb a s y + gbh a s y)| ≤ |c| * (Rpair aT sT Y a s * Gw aT sT y) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      linarith [neg_abs_le (c * (gb a s y + gbh a s y))]
    simp only [tailSum, gsum]
    nlinarith

/-- The tail constant of the wide pair's own `gbh` term. -/
noncomputable def RT (aT sT Y : ℝ) : ℝ :=
  2 / Real.sqrt aT * Real.exp (-π * (1 / aT) * (Y - 0) ^ 2 + π * aT * (Y - sT) ^ 2)

theorem tail_pos {aT sT cT Y : ℝ} {R : List (ℝ × ℝ × ℝ)} (haT : 0 < aT) (hcT : 0 < cT)
    (hT1 : aT ≤ 1 / aT) (hT2 : 1 / aT * 0 - aT * sT ≤ (1 / aT - aT) * Y)
    (hR : ∀ p ∈ R, PairCond aT sT Y p.1 p.2.1)
    (hbr : 0 < cT - cT * RT aT sT Y - tailSum aT sT Y R) :
    ∀ y, Y ≤ y → 0 < gsum ((aT, sT, cT) :: R) y := by
  intro y hy
  have hG : 0 < Gw aT sT y := Real.exp_pos _
  have hsq : 0 ≤ 2 / Real.sqrt aT := by positivity
  -- gbh_T ≥ -RT G
  have e3 : Real.exp (-π * y ^ 2 / aT) ≤
      Real.exp (-π * (1 / aT) * (Y - 0) ^ 2 + π * aT * (Y - sT) ^ 2) * Gw aT sT y :=
    exp_le_mul_Gw (aT := aT) (sT := sT) (y := y) (q := -π * y ^ 2 / aT)
      (e := -π * (1 / aT) * (y - 0) ^ 2 + π * aT * (y - sT) ^ 2) (by ring) (quad_le hT1 hT2 hy)
  have hbh : -(RT aT sT Y * Gw aT sT y) ≤ gbh aT sT y := by
    unfold gbh RT
    have hc := neg_one_le_cos (2 * π * sT * y)
    have hp : 0 ≤ 2 / Real.sqrt aT * Real.exp (-π * y ^ 2 / aT) := by positivity
    have := mul_le_mul_of_nonneg_left e3 hsq
    nlinarith
  have hgb : Gw aT sT y ≤ gb aT sT y := by
    unfold gb Gw; linarith [Real.exp_pos (-π * aT * (y + sT) ^ 2)]
  have hrest := gsum_ge_tail hy R hR
  simp only [gsum]
  have h1 : cT * (Gw aT sT y - RT aT sT Y * Gw aT sT y) ≤ cT * (gb aT sT y + gbh aT sT y) :=
    mul_le_mul_of_nonneg_left (by linarith) hcT.le
  have h2 : 0 < Gw aT sT y * (cT - cT * RT aT sT Y - tailSum aT sT Y R) := mul_pos hG hbr
  nlinarith

end SignUnc
