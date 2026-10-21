import SignUnc.Ival.SoundTrig

/-!
# Soundness of complex discs (`Ival.CDisc`)
-/

namespace Ival.CDisc

open Ball Complex

/-- `z` lies in the disc `D` at precision `P`. -/
def memC (P : ℕ) (z : ℂ) (D : CDisc) : Prop :=
  ‖z - ((D.cr : ℂ) + (D.ci : ℂ) * I) / 2 ^ P‖ ≤ (D.r : ℝ) / 2 ^ P

variable {P : ℕ}

theorem memC_ofBalls {x y : ℝ} {c s : Ball} (hx : Ball.mem P x c) (hy : Ball.mem P y s) :
    memC P ((x : ℂ) + (y : ℂ) * I) (ofBalls c s) := by
  unfold memC ofBalls
  unfold Ball.mem at hx hy
  have hP := Ball.two_pow_pos' P
  have e : ((x : ℂ) + (y : ℂ) * I) - (((c.m : ℂ) + (s.m : ℂ) * I) / 2 ^ P)
      = ((x - (c.m : ℝ) / 2 ^ P : ℝ) : ℂ) + ((y - (s.m : ℝ) / 2 ^ P : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e]
  calc ‖((x - (c.m : ℝ) / 2 ^ P : ℝ) : ℂ) + ((y - (s.m : ℝ) / 2 ^ P : ℝ) : ℂ) * I‖
      ≤ ‖((x - (c.m : ℝ) / 2 ^ P : ℝ) : ℂ)‖ + ‖((y - (s.m : ℝ) / 2 ^ P : ℝ) : ℂ) * I‖ := norm_add_le _ _
    _ = |x - (c.m : ℝ) / 2 ^ P| + |y - (s.m : ℝ) / 2 ^ P| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ (c.r : ℝ) / 2 ^ P + (s.r : ℝ) / 2 ^ P := add_le_add hx hy
    _ = ((c.r + s.r : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

theorem center_eq (D : CDisc) : ((D.cr : ℂ) + (D.ci : ℂ) * I) / 2 ^ P =
    (((D.cr : ℝ) / 2 ^ P : ℝ) : ℂ) + (((D.ci : ℝ) / 2 ^ P : ℝ) : ℂ) * I := by
  push_cast; ring

theorem mem_re {z : ℂ} {D : CDisc} (h : memC P z D) : Ball.mem P z.re D.re := by
  unfold memC at h
  unfold Ball.mem re
  rw [center_eq] at h
  have e : z.re - (D.cr : ℝ) / 2 ^ P =
      (z - ((((D.cr : ℝ) / 2 ^ P : ℝ) : ℂ) + (((D.ci : ℝ) / 2 ^ P : ℝ) : ℂ) * I)).re := by
    rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      add_zero]
  rw [e]
  exact (Complex.abs_re_le_norm _).trans h

theorem mem_im {z : ℂ} {D : CDisc} (h : memC P z D) : Ball.mem P z.im D.im := by
  unfold memC at h
  unfold Ball.mem im
  rw [center_eq] at h
  have e : z.im - (D.ci : ℝ) / 2 ^ P =
      (z - ((((D.cr : ℝ) / 2 ^ P : ℝ) : ℂ) + (((D.ci : ℝ) / 2 ^ P : ℝ) : ℂ) * I)).im := by
    rw [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  rw [e]
  exact (Complex.abs_im_le_norm _).trans h

/-- The modulus of the centre is at most `cabsHi / 2^P`. -/
theorem norm_center_le (D : CDisc) :
    ‖((D.cr : ℂ) + (D.ci : ℂ) * I) / 2 ^ P‖ ≤ (D.cabsHi P : ℝ) / 2 ^ P := by
  have hP := Ball.two_pow_pos' P
  set x : ℝ := ((D.cr : ℝ) ^ 2 + (D.ci : ℝ) ^ 2) / (2 ^ P) ^ 2 with hx
  have hnorm : ‖((D.cr : ℂ) + (D.ci : ℂ) * I) / 2 ^ P‖ = Real.sqrt x := by
    rw [center_eq, Complex.norm_eq_sqrt_sq_add_sq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, Complex.add_im, Complex.mul_im, zero_add, add_zero]
    rw [hx]
    congr 1
    field_simp
  rw [hnorm]
  have hsq : Real.sqrt x ≤ (1 + x) / 2 := by
    have h0 : 0 ≤ x := by positivity
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]
  have hc := Ball.cdiv_spec (2 ^ (2 * P) + (D.cr * D.cr + D.ci * D.ci).toNat) (2 * 2 ^ P) (by positivity)
  have htoNat : (((D.cr * D.cr + D.ci * D.ci).toNat : ℕ) : ℝ) = (D.cr : ℝ) ^ 2 + (D.ci : ℝ) ^ 2 := by
    have h0 : 0 ≤ D.cr * D.cr + D.ci * D.ci := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have := Int.toNat_of_nonneg h0
    have h2 : (((D.cr * D.cr + D.ci * D.ci).toNat : ℕ) : ℤ) = D.cr * D.cr + D.ci * D.ci := this
    have h3 := congrArg (fun t : ℤ => (t : ℝ)) h2
    push_cast at h3
    rw [h3]; ring
  unfold cabsHi
  calc Real.sqrt x ≤ (1 + x) / 2 := hsq
    _ = (((2 ^ (2 * P) + (D.cr * D.cr + D.ci * D.ci).toNat : ℕ) : ℝ) / ((2 * 2 ^ P : ℕ) : ℝ)) / 2 ^ P := by
        rw [hx]; push_cast; rw [htoNat]
        rw [show (2 : ℝ) ^ (2 * P) = (2 ^ P) ^ 2 by rw [← pow_mul, mul_comm]]
        field_simp
    _ ≤ (cdiv (2 ^ (2 * P) + (D.cr * D.cr + D.ci * D.ci).toNat) (2 * 2 ^ P) : ℝ) / 2 ^ P := by gcongr

theorem memC_mul {z w : ℂ} {Z W : CDisc} (hz : memC P z Z) (hw : memC P w W) :
    memC P (z * w) (mul P Z W) := by
  unfold memC at hz hw ⊢
  have hP := Ball.two_pow_pos' P
  set a : ℂ := ((Z.cr : ℂ) + (Z.ci : ℂ) * I) / 2 ^ P
  set b : ℂ := ((W.cr : ℂ) + (W.ci : ℂ) * I) / 2 ^ P
  have ha := norm_center_le (P := P) Z
  have hb := norm_center_le (P := P) W
  -- |zw - ab|
  have key : ‖z * w - a * b‖ ≤ (Z.cabsHi P : ℝ) / 2 ^ P * ((W.r : ℝ) / 2 ^ P) +
      (W.cabsHi P : ℝ) / 2 ^ P * ((Z.r : ℝ) / 2 ^ P) + (Z.r : ℝ) / 2 ^ P * ((W.r : ℝ) / 2 ^ P) := by
    have e : z * w - a * b = a * (w - b) + b * (z - a) + (z - a) * (w - b) := by ring
    rw [e]
    calc ‖a * (w - b) + b * (z - a) + (z - a) * (w - b)‖
        ≤ ‖a * (w - b)‖ + ‖b * (z - a)‖ + ‖(z - a) * (w - b)‖ := norm_add₃_le
      _ = ‖a‖ * ‖w - b‖ + ‖b‖ * ‖z - a‖ + ‖z - a‖ * ‖w - b‖ := by rw [norm_mul, norm_mul, norm_mul]
      _ ≤ _ := by gcongr
  -- the rounded centre
  set p1 : ℤ := Z.cr * W.cr - Z.ci * W.ci
  set p2 : ℤ := Z.cr * W.ci + Z.ci * W.cr
  have hab : a * b = (((p1 : ℂ) / 2 ^ P) + ((p2 : ℂ) / 2 ^ P) * I) / 2 ^ P := by
    simp only [a, b, p1, p2]; push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring
  have hr1 := Ball.rnd2_spec p1 P
  have hr2 := Ball.rnd2_spec p2 P
  have hround : ‖a * b - (((Ball.rnd2 p1 P : ℤ) : ℂ) + ((Ball.rnd2 p2 P : ℤ) : ℂ) * I) / 2 ^ P‖ ≤ 2 / 2 ^ P := by
    rw [hab]
    have e : ((p1 : ℂ) / 2 ^ P + (p2 : ℂ) / 2 ^ P * I) / 2 ^ P -
        (((Ball.rnd2 p1 P : ℤ) : ℂ) + ((Ball.rnd2 p2 P : ℤ) : ℂ) * I) / 2 ^ P =
        ((((p1 : ℝ) / 2 ^ P - (Ball.rnd2 p1 P : ℝ) : ℝ) : ℂ) +
          (((p2 : ℝ) / 2 ^ P - (Ball.rnd2 p2 P : ℝ) : ℝ) : ℂ) * I) / 2 ^ P := by
      push_cast; ring
    rw [e, norm_div]
    have h2P : ‖(2 : ℂ) ^ P‖ = 2 ^ P := by rw [norm_pow]; simp
    rw [h2P]
    apply div_le_div_of_nonneg_right _ hP.le
    calc ‖((((p1 : ℝ) / 2 ^ P - (Ball.rnd2 p1 P : ℝ) : ℝ) : ℂ) +
          (((p2 : ℝ) / 2 ^ P - (Ball.rnd2 p2 P : ℝ) : ℝ) : ℂ) * I)‖
        ≤ ‖(((p1 : ℝ) / 2 ^ P - (Ball.rnd2 p1 P : ℝ) : ℝ) : ℂ)‖ +
          ‖(((p2 : ℝ) / 2 ^ P - (Ball.rnd2 p2 P : ℝ) : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |(p1 : ℝ) / 2 ^ P - (Ball.rnd2 p1 P : ℝ)| + |(p2 : ℝ) / 2 ^ P - (Ball.rnd2 p2 P : ℝ)| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ 1 + 1 := add_le_add hr1 hr2
      _ = 2 := by norm_num
  set N := Z.cabsHi P * W.r + W.cabsHi P * Z.r + Z.r * W.r
  have hN : (Z.cabsHi P : ℝ) / 2 ^ P * ((W.r : ℝ) / 2 ^ P) + (W.cabsHi P : ℝ) / 2 ^ P * ((Z.r : ℝ) / 2 ^ P) +
      (Z.r : ℝ) / 2 ^ P * ((W.r : ℝ) / 2 ^ P) = ((N : ℝ) / 2 ^ P) / 2 ^ P := by
    simp only [N]; push_cast; field_simp
  have hc := Ball.cdiv_spec N (2 ^ P) (by positivity)
  unfold mul
  simp only
  calc ‖z * w - (((Ball.rnd2 p1 P : ℤ) : ℂ) + ((Ball.rnd2 p2 P : ℤ) : ℂ) * I) / 2 ^ P‖
      ≤ ‖z * w - a * b‖ + ‖a * b - (((Ball.rnd2 p1 P : ℤ) : ℂ) + ((Ball.rnd2 p2 P : ℤ) : ℂ) * I) / 2 ^ P‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((N : ℝ) / 2 ^ P) / 2 ^ P + 2 / 2 ^ P := add_le_add (key.trans hN.le) hround
    _ ≤ (cdiv N (2 ^ P) : ℝ) / 2 ^ P + 2 / 2 ^ P := by
        push_cast at hc
        gcongr
    _ = ((cdiv N (2 ^ P) + 2 : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

end Ival.CDisc
