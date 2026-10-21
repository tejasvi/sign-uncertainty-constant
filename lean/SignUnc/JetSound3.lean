import SignUnc.JetSound2

/-!
# Soundness of checker v4, part 3: the terms of a group and `groupJet`
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex Finset

variable {P : ℕ}

/-! ## The terms as quadratic exponentials -/

/-- `c e^{-πa(y-s)²}` as `Re(K exp(B y² + C y + D))`. -/
noncomputable def quadE (a c s : ℝ) : ℂ × ℂ × ℂ × ℂ :=
  ((c : ℂ), ((-(π * a) : ℝ) : ℂ), ((2 * π * a * s : ℝ) : ℂ), ((-(π * a) * s ^ 2 : ℝ) : ℂ))

/-- `c e^{-πa(y+s)²}`. -/
noncomputable def quadF (a c s : ℝ) : ℂ × ℂ × ℂ × ℂ := quadE a c (-s)

/-- `c 2a^{-1/2} e^{-πy²/a} cos(2πsy)`. -/
noncomputable def quadH (a c s : ℝ) : ℂ × ℂ × ℂ × ℂ :=
  ((((c * (2 / Real.sqrt a)) : ℝ) : ℂ), ((-(π * (1 / a)) : ℝ) : ℂ), ((2 * π * s : ℝ) : ℂ) * I, 0)

noncomputable def tauQ (q : ℂ × ℂ × ℂ × ℂ) (j : ℕ) (y : ℝ) : ℝ := tau q.1 q.2.1 q.2.2.1 q.2.2.2 j y

theorem tauSum_eq (L : List (ℂ × ℂ × ℂ × ℂ)) (j : ℕ) (y : ℝ) : tauSum L j y = (L.map fun q => tauQ q j y).sum := rfl

theorem tauSum_append (L1 L2 : List (ℂ × ℂ × ℂ × ℂ)) (j : ℕ) (y : ℝ) :
    tauSum (L1 ++ L2) j y = tauSum L1 j y + tauSum L2 j y := by
  simp [tauSum, List.map_append, List.sum_append]

theorem ecoef_ofReal (α β : ℝ) (j : ℕ) : ecoef (α : ℂ) (β : ℂ) j = ((ecoef α β j : ℝ) : ℂ) := by
  simpa using (ecoef_map Complex.ofRealHom α β j).symm

theorem tau_quadE (a c s : ℝ) (j : ℕ) (y : ℝ) :
    tauQ (quadE a c s) j y = c * Real.exp (-π * a * (y - s) ^ 2) * ecoef (-(2 * (π * a)) * (y - s)) (-(π * a)) j := by
  unfold tauQ tau quadE
  have h1 : ((-(π * a) : ℝ) : ℂ) * (y : ℂ) ^ 2 + ((2 * π * a * s : ℝ) : ℂ) * y + ((-(π * a) * s ^ 2 : ℝ) : ℂ) =
      ((-π * a * (y - s) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : 2 * ((-(π * a) : ℝ) : ℂ) * (y : ℂ) + ((2 * π * a * s : ℝ) : ℂ) = ((-(2 * (π * a)) * (y - s) : ℝ) : ℂ) := by
    push_cast; ring
  simp only
  rw [h1, h2, ← Complex.ofReal_exp, ecoef_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem tau_quadF (a c s : ℝ) (j : ℕ) (y : ℝ) :
    tauQ (quadF a c s) j y = c * Real.exp (-π * a * (y + s) ^ 2) * ecoef (-(2 * (π * a)) * (y + s)) (-(π * a)) j := by
  unfold quadF; rw [tau_quadE]; simp only [sub_neg_eq_add]

theorem re_mul_I_pow (c ω θ : ℝ) (p : ℕ) :
    ((c : ℂ) * Complex.exp ((θ : ℂ) * I) * ((ω : ℂ) * I) ^ p).re =
      pw2R (c * Real.cos θ) (-(ω * (c * Real.sin θ))) (-(ω * ω)) p := by
  rw [exp_I_eq]
  unfold pw2R
  rcases Nat.even_or_odd p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have h1 : (q + q) % 2 = 0 := by omega
    have h2 : (q + q) / 2 = q := by omega
    rw [if_pos h1, h2, ← two_mul, pow_mul]
    have e : ((ω : ℂ) * I) ^ 2 = ((-(ω * ω) : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
    rw [e, ← Complex.ofReal_pow]
    simp only [mul_re, ofReal_re, ofReal_im, add_re, add_im, mul_im, I_re, I_im]
    ring
  · have h1 : (2 * q + 1) % 2 = 1 := by omega
    have h2 : (2 * q + 1) / 2 = q := by omega
    rw [if_neg (by omega), h2, pow_succ, pow_mul]
    have e : ((ω : ℂ) * I) ^ 2 = ((-(ω * ω) : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
    rw [e, ← Complex.ofReal_pow]
    simp only [mul_re, ofReal_re, ofReal_im, add_re, add_im, mul_im, I_re, I_im]
    ring

theorem tau_quadH (a c s : ℝ) (j : ℕ) (y : ℝ) :
    tauQ (quadH a c s) j y = 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
      ∑ p ∈ range (j + 1), ecoef (-(2 * π * (y * (1 / a)))) (-(π * (1 / a))) (j - p) *
        pw2R (c * Real.cos (2 * π * s * y)) (-((2 * π * s) * (c * Real.sin (2 * π * s * y))))
          (-((2 * π * s) * (2 * π * s))) p / (p.factorial : ℝ) := by
  unfold tauQ tau quadH
  simp only
  have h1 : ((-(π * (1 / a)) : ℝ) : ℂ) * (y : ℂ) ^ 2 + ((2 * π * s : ℝ) : ℂ) * I * y + 0 =
      ((-π * y ^ 2 / a : ℝ) : ℂ) + ((2 * π * s * y : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : 2 * ((-(π * (1 / a)) : ℝ) : ℂ) * (y : ℂ) + ((2 * π * s : ℝ) : ℂ) * I =
      ((-(2 * π * (y * (1 / a))) : ℝ) : ℂ) + ((2 * π * s : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, h2, Complex.exp_add, ← Complex.ofReal_exp, ecoef_add, ecoefS, mul_sum, mul_sum, Complex.re_sum, mul_sum]
  refine sum_congr rfl (fun p _ => ?_)
  rw [ecoef_ofReal]
  have := re_mul_I_pow c (2 * π * s) (2 * π * s * y) p
  set e := ecoef (-(2 * π * (y * (1 / a)))) (-(π * (1 / a))) (j - p)
  set H := Real.exp (-π * y ^ 2 / a)
  have hre : (((c * (2 / Real.sqrt a)) : ℝ) : ℂ) * (((H : ℝ) : ℂ) * Complex.exp (((2 * π * s * y : ℝ) : ℂ) * I) *
      (((e : ℝ) : ℂ) * (((2 * π * s : ℝ) : ℂ) * I) ^ p / ((p.factorial : ℕ) : ℂ))) =
      (((2 / Real.sqrt a * H * e / (p.factorial : ℝ)) : ℝ) : ℂ) *
        ((c : ℂ) * Complex.exp (((2 * π * s * y : ℝ) : ℂ) * I) * (((2 * π * s : ℝ) : ℂ) * I) ^ p) := by
    push_cast; ring
  rw [hre, Complex.re_ofReal_mul, this]
  ring

/-! ## Sums of terms over rows -/

theorem listSum_ecoef (L : List (ℝ × ℝ)) (β : ℝ) (j : ℕ) :
    (L.map fun r => r.1 * ecoef r.2 β j).sum =
      ∑ p ∈ range (j + 1), momR L p / (p.factorial : ℝ) * ecoef 0 β (j - p) := by
  induction L with
  | nil => simp [momR]
  | cons r L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    have : ecoef r.2 β j = ecoef (0 + r.2) β j := by rw [zero_add]
    rw [this, ecoef_add, ecoefS, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun p _ => ?_)
    simp only [momR, List.map_cons, List.sum_cons]
    ring

theorem listSum_pw2 (L : List (ℝ × ℝ × ℝ)) (e : ℕ → ℝ) (j : ℕ) :
    (L.map fun r => ∑ p ∈ range (j + 1), e (j - p) * pw2R r.1 r.2.1 r.2.2 p / (p.factorial : ℝ)).sum =
      ∑ p ∈ range (j + 1), momR2 L p / (p.factorial : ℝ) * e (j - p) := by
  induction L with
  | nil => simp [momR2]
  | cons r L ih =>
    rw [List.map_cons, List.sum_cons, ih, ← sum_add_distrib]
    refine sum_congr rfl (fun p _ => ?_)
    simp only [momR2, List.map_cons, List.sum_cons]
    ring

end SignUnc.Chk
