import SignUnc.LowSound5

/-!
# Soundness of the lower checker, part 6: `P̂` for large `y` (exact integration by parts of the pieces)

For a chain of functions `F₀, F₁, …` with `F_l' = F_{l+1}` and `F_{D+1} = 0`,
`∫_a^b F₀(t) e^{iωt} dt = [Σ_{l ≤ D} (-1)^l F_l(t) e^{iωt} / (iω)^{l+1}]_a^b`.  Applied to the derivatives `PD l` of the
polynomial pieces and regrouped at the knots, `|P̂(y)| ≤ 2 (jumpsAll + jumpsEnd) / 2^P` for `y ≥ Y` (at the knot `0`
only odd `l` contribute to the real part).
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Complex Finset MeasureTheory intervalIntegral

variable {P : ℕ}

/-! ## Derivatives of a piece in `t` -/

/-- The `l`-th derivative of a piece: `Σ_i (B_i/2^P) i^(l) ((t-c)/η)^(i-l) / η^l` (falling factorial `i^(l)`). -/
noncomputable def PD (P : ℕ) (pc : PPiece) (l : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range pc.2.2.length, ((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P * (i.descFactorial l : ℝ) *
    ((t - pcR pc) / peR pc) ^ (i - l) / peR pc ^ l

theorem PD_zero (pc : PPiece) (t : ℝ) : PD P pc 0 t = Peval P pc t := by
  unfold PD Peval
  refine sum_congr rfl (fun i _ => ?_)
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.sub_zero, pow_zero, div_one]
  rfl

theorem PD_top {pc : PPiece} {D : ℕ} (hlen : pc.2.2.length = D + 1) (t : ℝ) : PD P pc (D + 1) t = 0 := by
  unfold PD
  refine sum_eq_zero (fun i hi => ?_)
  rw [hlen, mem_range] at hi
  rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hi]
  simp

theorem hasDerivAt_PD {pc : PPiece} (hlt : pc.1 < pc.2.1) (l : ℕ) (t : ℝ) :
    HasDerivAt (PD P pc l) (PD P pc (l + 1) t) t := by
  have he := (peR_pos hlt).ne'
  have key : ∀ i ∈ range pc.2.2.length, HasDerivAt (fun t => ((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P *
      (i.descFactorial l : ℝ) * ((t - pcR pc) / peR pc) ^ (i - l) / peR pc ^ l)
      (((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P * (i.descFactorial (l + 1) : ℝ) *
        ((t - pcR pc) / peR pc) ^ (i - (l + 1)) / peR pc ^ (l + 1)) t := by
    intro i _
    have h1 : HasDerivAt (fun t => (t - pcR pc) / peR pc) (1 / peR pc) t :=
      ((hasDerivAt_id t).sub_const _).div_const _
    have h2 := ((h1.pow (i - l)).const_mul (((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P * (i.descFactorial l : ℝ))).div_const
      (peR pc ^ l)
    convert h2 using 1
    rcases Nat.lt_or_ge i (l + 1) with hil | hil
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hil]
      have : i - l = 0 := by omega
      simp [this]
    · rw [Nat.descFactorial_succ, show i - (l + 1) = i - l - 1 by omega, Nat.cast_mul]
      field_simp
      ring
  have := HasDerivAt.sum key
  unfold PD
  convert this using 1
  · funext t; simp

theorem pcR_add_peR {pc : PPiece} (h : pc.1 ≤ pc.2.1) : phi' pc = pcR pc + peR pc := by
  rw [phi_eq h]; ring

theorem pcR_sub_peR {pc : PPiece} (h : pc.1 ≤ pc.2.1) : plo pc = pcR pc - peR pc := by
  rw [plo_eq h]; ring

/-- `derivPM` as a sum. -/
theorem derivPM_foldr (l : ℕ) (sgn : Bool) : ∀ (bs : List ℤ) (s : ℕ),
    ((((List.range' s bs.length).zip bs).foldr (fun ib acc =>
      if l ≤ ib.1 then
        acc + ib.2 * ((fact ib.1 / fact (ib.1 - l) : ℕ) : ℤ) * (if sgn && (ib.1 - l) % 2 = 1 then -1 else 1)
      else acc) 0 : ℤ) : ℝ) =
    ∑ i ∈ range bs.length, ((bs.getD i 0 : ℤ) : ℝ) * ((s + i).descFactorial l : ℝ) *
      (if sgn then (-1 : ℝ) ^ (s + i - l) else 1)
  | [], s => by simp
  | b :: bs, s => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldr_cons, sum_range_succ']
    have ih := derivPM_foldr l sgn bs (s + 1)
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    have e : ∀ i, s + 1 + i = s + (i + 1) := fun i => by ring
    simp only [e] at ih
    by_cases hl : l ≤ s
    · rw [if_pos hl, Int.cast_add, ih]
      congr 1
      rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, fact_eq, fact_eq, ← Nat.descFactorial_eq_div hl]
      congr 1
      cases sgn
      · simp
      · rcases Nat.even_or_odd (s - l) with he | ho
        · have : (s - l) % 2 = 0 := Nat.even_iff.mp he
          simp [this, he.neg_one_pow]
        · have : (s - l) % 2 = 1 := Nat.odd_iff.mp ho
          simp [this, ho.neg_one_pow]
    · rw [if_neg hl, ih, (Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]
      simp

theorem derivPM_cast (bs : List ℤ) (l : ℕ) (sgn : Bool) :
    ((derivPM bs l sgn : ℤ) : ℝ) = ∑ i ∈ range bs.length, ((bs.getD i 0 : ℤ) : ℝ) * (i.descFactorial l : ℝ) *
      (if sgn then (-1 : ℝ) ^ (i - l) else 1) := by
  unfold derivPM
  rw [List.range_eq_range', derivPM_foldr l sgn bs 0]
  simp

theorem PD_hi {pc : PPiece} (hlt : pc.1 < pc.2.1) (l : ℕ) :
    PD P pc l (phi' pc) = ((derivPM pc.2.2 l false : ℤ) : ℝ) / 2 ^ P / peR pc ^ l := by
  have he := (peR_pos hlt).ne'
  rw [derivPM_cast, PD, pcR_add_peR hlt.le, add_sub_cancel_left, div_self he, sum_div, sum_div]
  refine sum_congr rfl (fun i _ => ?_)
  simp only [one_pow, mul_one, Bool.false_eq_true, if_false]
  ring

theorem PD_lo {pc : PPiece} (hlt : pc.1 < pc.2.1) (l : ℕ) :
    PD P pc l (plo pc) = ((derivPM pc.2.2 l true : ℤ) : ℝ) / 2 ^ P / peR pc ^ l := by
  have he := (peR_pos hlt).ne'
  rw [derivPM_cast, PD, pcR_sub_peR hlt.le, show pcR pc - peR pc - pcR pc = -peR pc by ring, neg_div, div_self he,
    sum_div, sum_div]
  refine sum_congr rfl (fun i _ => ?_)
  simp only [if_true]
  ring

/-! ## Integration by parts against `e^{iωt}` -/

/-- `Σ_{l ≤ D} (-1)^l F_l(t) e^{iωt} / (iω)^{l+1}`. -/
noncomputable def ibpA (D : ℕ) (F : ℕ → ℝ → ℝ) (ω t : ℝ) : ℂ :=
  ∑ l ∈ range (D + 1), (-1 : ℂ) ^ l * (F l t : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I) / ((ω : ℂ) * I) ^ (l + 1)

theorem hasDerivAt_ibpA {D : ℕ} {F : ℕ → ℝ → ℝ} (hF : ∀ l ≤ D, ∀ t, HasDerivAt (F l) (F (l + 1) t) t)
    (hD : ∀ t, F (D + 1) t = 0) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (ibpA D F ω) ((F 0 t : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I)) t := by
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have hI : I ≠ 0 := Complex.I_ne_zero
  have hwI : (ω : ℂ) * I ≠ 0 := mul_ne_zero hω' hI
  set E : ℝ → ℂ := fun t => Complex.exp (((ω * t : ℝ) : ℂ) * I) with hE
  have hEd : ∀ t, HasDerivAt E (E t * ((ω : ℂ) * I)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((ω * t : ℝ) : ℂ) * I) ((ω : ℂ) * I) t := by
      have := (((hasDerivAt_id t).const_mul ω).ofReal_comp).mul_const I
      simpa using this
    exact h1.cexp
  have hterm : ∀ l ∈ range (D + 1), HasDerivAt
      (fun y => (-1 : ℂ) ^ l * ((F l y : ℂ) * E y) / ((ω : ℂ) * I) ^ (l + 1))
      ((-1 : ℂ) ^ l * ((F (l + 1) t : ℂ) * E t + (F l t : ℂ) * (E t * ((ω : ℂ) * I))) / ((ω : ℂ) * I) ^ (l + 1)) t := by
    intro l hl
    have hl' : l ≤ D := by rw [mem_range] at hl; omega
    have h1 : HasDerivAt (fun y => (F l y : ℂ)) (F (l + 1) t : ℂ) t := (hF l hl' t).ofReal_comp
    exact ((h1.mul (hEd t)).const_mul ((-1 : ℂ) ^ l)).div_const (((ω : ℂ) * I) ^ (l + 1))
  have hsum := HasDerivAt.sum hterm
  have hfun : ibpA D F ω =
      ∑ l ∈ range (D + 1), fun y => (-1 : ℂ) ^ l * ((F l y : ℂ) * E y) / ((ω : ℂ) * I) ^ (l + 1) := by
    funext y
    rw [Finset.sum_apply]
    unfold ibpA
    refine sum_congr rfl (fun l _ => ?_)
    simp only [hE]
    ring
  rw [hfun]
  refine hsum.congr_deriv ?_
  set a : ℕ → ℂ := fun l => (-1 : ℂ) ^ l * (F l t : ℂ) * E t / ((ω : ℂ) * I) ^ l with ha
  have e : ∀ l ∈ range (D + 1), (-1 : ℂ) ^ l * ((F (l + 1) t : ℂ) * E t + (F l t : ℂ) * (E t * ((ω : ℂ) * I))) /
      ((ω : ℂ) * I) ^ (l + 1) = a l - a (l + 1) := by
    intro l _
    simp only [ha]
    rw [pow_succ, pow_succ]
    field_simp
    ring
  rw [sum_congr rfl e, sum_range_sub']
  simp only [ha, pow_zero, div_one, one_mul, hD, Complex.ofReal_zero, mul_zero, zero_mul, zero_div, sub_zero]
  rfl

theorem integral_ibp {D : ℕ} {F : ℕ → ℝ → ℝ} (hF : ∀ l ≤ D, ∀ t, HasDerivAt (F l) (F (l + 1) t) t)
    (hD : ∀ t, F (D + 1) t = 0) {ω : ℝ} (hω : ω ≠ 0) (a b : ℝ) :
    ∫ t in a..b, (F 0 t : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I) = ibpA D F ω b - ibpA D F ω a := by
  have hc : Continuous (F 0) := continuous_iff_continuousAt.mpr (fun t => (hF 0 (Nat.zero_le _) t).continuousAt)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_ibpA hF hD hω t) ?_
  exact (by fun_prop : Continuous fun t => (F 0 t : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I)).intervalIntegrable _ _

/-- `∫ f cos(ωt) = Re ∫ f e^{iωt}`. -/
theorem integral_cos_re {f : ℝ → ℝ} (hf : Continuous f) (ω a b : ℝ) :
    ∫ t in a..b, f t * Real.cos (ω * t) = (∫ t in a..b, (f t : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I)).re := by
  have hi : IntervalIntegrable (fun t => (f t : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I)) volume a b :=
    (by fun_prop : Continuous fun t => (f t : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I)).intervalIntegrable _ _
  have := Complex.reCLM.intervalIntegral_comp_comm hi
  rw [Complex.reCLM_apply] at this
  rw [← this]
  congr 1; funext t
  rw [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-! ## The pieces of `P̂` at large `y` -/

/-- The IBP antiderivative of a piece. -/
noncomputable def pieceA (P D : ℕ) (pc : PPiece) (ω t : ℝ) : ℂ := ibpA D (PD P pc) ω t

theorem piece_ibp {pc : PPiece} (hlt : pc.1 < pc.2.1) {D : ℕ} (hlen : pc.2.2.length = D + 1) {ω : ℝ} (hω : ω ≠ 0) :
    2 * ∫ t in plo pc..phi' pc, Peval P pc t * Real.cos (ω * t) =
      2 * (pieceA P D pc ω (phi' pc) - pieceA P D pc ω (plo pc)).re := by
  rw [integral_cos_re (continuous_Peval pc)]
  have := integral_ibp (D := D) (F := PD P pc) (fun l _ t => hasDerivAt_PD hlt l t) (fun t => PD_top hlen t) hω
    (plo pc) (phi' pc)
  simp only [PD_zero] at this
  rw [this]; rfl

/-- The value of the antiderivative at a knot from the end derivatives `S_l / 2^P / η^l`. -/
noncomputable def knotA (P D : ℕ) (S : ℕ → ℤ) (w : ℕ) (ω t : ℝ) : ℂ :=
  ∑ l ∈ range (D + 1), (-1 : ℂ) ^ l * ((((S l : ℤ) : ℝ) / 2 ^ P * ((20000 : ℝ) / w) ^ l : ℝ) : ℂ) *
    Complex.exp (((ω * t : ℝ) : ℂ) * I) / ((ω : ℂ) * I) ^ (l + 1)

theorem peR_eq_w (pc : PPiece) (hle : pc.1 ≤ pc.2.1) : peR pc = (((pc.2.1 - pc.1 : ℕ) : ℝ)) / 20000 := rfl

theorem pieceA_hi {pc : PPiece} (hlt : pc.1 < pc.2.1) (D : ℕ) (ω : ℝ) :
    pieceA P D pc ω (phi' pc) = knotA P D (fun l => derivPM pc.2.2 l false) (pc.2.1 - pc.1) ω (phi' pc) := by
  unfold pieceA ibpA knotA
  refine sum_congr rfl (fun l _ => ?_)
  rw [PD_hi hlt, peR_eq_w pc hlt.le]
  have hw : (((pc.2.1 - pc.1 : ℕ) : ℝ)) ≠ 0 := by
    have : 0 < pc.2.1 - pc.1 := by omega
    positivity
  congr 3
  congr 1
  simp only []
  rw [div_pow, div_pow]
  field_simp

theorem pieceA_lo {pc : PPiece} (hlt : pc.1 < pc.2.1) (D : ℕ) (ω : ℝ) :
    pieceA P D pc ω (plo pc) = knotA P D (fun l => derivPM pc.2.2 l true) (pc.2.1 - pc.1) ω (plo pc) := by
  unfold pieceA ibpA knotA
  refine sum_congr rfl (fun l _ => ?_)
  rw [PD_lo hlt, peR_eq_w pc hlt.le]
  have hw : (((pc.2.1 - pc.1 : ℕ) : ℝ)) ≠ 0 := by
    have : 0 < pc.2.1 - pc.1 := by omega
    positivity
  congr 3
  congr 1
  simp only []
  rw [div_pow, div_pow]
  field_simp

/-! ## Bounds at the knots -/

theorem norm_wI_pow {ω : ℝ} (hω : 0 < ω) (n : ℕ) : ‖((ω : ℂ) * I) ^ n‖ = ω ^ n := by
  rw [norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]

/-- `|Re(c e^{iωt} (-1)^l / (iω)^(l+1))| ≤ |c| / ω^(l+1)`. -/
theorem abs_re_term_le {ω : ℝ} (hω : 0 < ω) (c t : ℝ) (l : ℕ) :
    |((-1 : ℂ) ^ l * (c : ℂ) * Complex.exp (((ω * t : ℝ) : ℂ) * I) / ((ω : ℂ) * I) ^ (l + 1)).re| ≤
      |c| / ω ^ (l + 1) := by
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, norm_wI_pow hω]

/-- At `t = 0` and even `l` the term is purely imaginary. -/
theorem re_term_zero_even {ω : ℝ} (c : ℝ) {l : ℕ} (hl : l % 2 = 0) :
    ((-1 : ℂ) ^ l * (c : ℂ) * Complex.exp (((ω * 0 : ℝ) : ℂ) * I) / ((ω : ℂ) * I) ^ (l + 1)).re = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, l = 2 * q := ⟨l / 2, by omega⟩
  have hI : ((ω : ℂ) * I) ^ (2 * q + 1) = (((-1) ^ q * ω ^ (2 * q + 1) : ℝ) : ℂ) * I := by
    rw [mul_pow, pow_succ I, pow_mul, Complex.I_sq]; push_cast; ring
  rw [hI, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, pow_mul, neg_one_sq, one_pow, one_mul]
  rcases eq_or_ne ((-1) ^ q * ω ^ (2 * q + 1) : ℝ) 0 with h0 | h0
  · rw [h0, Complex.ofReal_zero, zero_mul, div_zero, Complex.zero_re]
  · rw [div_mul_eq_div_div, show (c : ℂ) / (((-1) ^ q * ω ^ (2 * q + 1) : ℝ) : ℂ) =
        ((c / ((-1) ^ q * ω ^ (2 * q + 1)) : ℝ) : ℂ) by push_cast; ring, Complex.div_I, Complex.neg_re,
      Complex.re_ofReal_mul, Complex.I_re, mul_zero, neg_zero]

theorem pi_bound {YT : ℕ} {y : ℝ} (hy : (YT : ℝ) ≤ y) : 2 * (3141592 / 1000000) * (YT : ℝ) ≤ 2 * π * y := by
  have h1 : (3141592 / 1000000 : ℝ) < π := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have h0 : (0 : ℝ) ≤ YT := by positivity
  nlinarith

/-- One `jumpTerm` bounds one knot term (`y ≥ Y`). -/
theorem jumpTerm_bound {YT : ℕ} (hYT : 0 < YT) {y : ℝ} (hy : (YT : ℝ) ≤ y) (l : ℕ) (S1 : ℤ) (w1 : ℕ) (S2 : ℤ) (w2 : ℕ)
    (hw1 : 0 < w1) (hw2 : 0 < w2) :
    |(S1 : ℝ) / 2 ^ P * ((20000 : ℝ) / w1) ^ l - (S2 : ℝ) / 2 ^ P * ((20000 : ℝ) / w2) ^ l| / (2 * π * y) ^ (l + 1) ≤
      (jumpTerm P YT l S1 w1 S2 w2 : ℝ) / 2 ^ P := by
  unfold jumpTerm
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  set num : ℤ := (S1 * ((w2 ^ l : ℕ) : ℤ) - S2 * ((w1 ^ l : ℕ) : ℤ)) * ((20000 ^ l * 1000000 ^ (l + 1) : ℕ) : ℤ)
    with hnum
  set den : ℕ := (w1 * w2) ^ l * (2 * 3141592 * YT) ^ (l + 1) * 2 ^ P with hden
  have hden0 : 0 < den := by positivity
  have h := abs_le_absHi (mem_ofRat P (num.natAbs : ℤ) den hden0)
  refine le_trans ?_ ((le_abs_self _).trans h)
  have hw1' : (0 : ℝ) < w1 := by exact_mod_cast hw1
  have hw2' : (0 : ℝ) < w2 := by exact_mod_cast hw2
  have hw1n : (w1 : ℝ) ≠ 0 := hw1'.ne'
  have hw2n : (w2 : ℝ) ≠ 0 := hw2'.ne'
  have hYT' : (0 : ℝ) < YT := by exact_mod_cast hYT
  have hpb := pi_bound hy
  have hB : 2 * (3141592 / 1000000) * (YT : ℝ) = (2 * 3141592 * (YT : ℝ)) / 1000000 := by ring
  rw [hB] at hpb
  have hc0 : (0 : ℝ) < 2 * 3141592 * (YT : ℝ) / 1000000 := by positivity
  have hpow : (2 * 3141592 * (YT : ℝ) / 1000000) ^ (l + 1) ≤ (2 * π * y) ^ (l + 1) :=
    pow_le_pow_left₀ hc0.le hpb _
  set A : ℝ := (S1 : ℝ) * w2 ^ l - S2 * w1 ^ l with hA
  have hX : (S1 : ℝ) / 2 ^ P * ((20000 : ℝ) / w1) ^ l - (S2 : ℝ) / 2 ^ P * ((20000 : ℝ) / w2) ^ l =
      A * 20000 ^ l / ((w1 * w2) ^ l * 2 ^ P) := by
    rw [hA, div_pow, div_pow]; field_simp; ring
  have e1 : ((num.natAbs : ℤ) : ℝ) / (den : ℝ) =
      |(S1 : ℝ) / 2 ^ P * ((20000 : ℝ) / w1) ^ l - (S2 : ℝ) / 2 ^ P * ((20000 : ℝ) / w2) ^ l| /
        (2 * 3141592 * (YT : ℝ) / 1000000) ^ (l + 1) := by
    rw [Int.natCast_natAbs, Int.cast_abs, hX, hnum, hden]
    have hnumR : (((S1 * ((w2 ^ l : ℕ) : ℤ) - S2 * ((w1 ^ l : ℕ) : ℤ)) * ((20000 ^ l * 1000000 ^ (l + 1) : ℕ) : ℤ) : ℤ) : ℝ) =
        A * ((20000 : ℝ) ^ l * 1000000 ^ (l + 1)) := by
      rw [hA]; push_cast; ring
    have hdenR : (((w1 * w2) ^ l * (2 * 3141592 * YT) ^ (l + 1) * 2 ^ P : ℕ) : ℝ) =
        ((w1 : ℝ) * w2) ^ l * (2 * 3141592 * (YT : ℝ)) ^ (l + 1) * 2 ^ P := by push_cast; ring
    rw [hnumR, hdenR, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (20000 : ℝ) ^ l * 1000000 ^ (l + 1)),
      abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (20000 : ℝ) ^ l),
      abs_of_pos (by positivity : (0 : ℝ) < ((w1 : ℝ) * w2) ^ l * 2 ^ P), div_pow]
    field_simp
  rw [e1]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hpow

/-! ## Regrouping at the knots -/

/-- The pending value at a knot `t`: `0` at the start (`w = 0`), else the right end of the previous piece. -/
noncomputable def pendA (P D : ℕ) (w : ℕ) (bs : List ℤ) (ω t : ℝ) : ℂ :=
  if w = 0 then 0 else knotA P D (fun l => derivPM bs l false) w ω t

/-- The knot terms of one piece. -/
theorem knot_bound {P D YT : ℕ} (hYT : 0 < YT) {y : ℝ} (hy : (YT : ℝ) ≤ y) (wprev : ℕ) (bprev : List ℤ)
    (pc : PPiece) (hlt : pc.1 < pc.2.1) {t : ℝ} (ht : wprev = 0 → t = 0) :
    |(pendA P D wprev bprev (2 * π * y) t -
        knotA P D (fun l => derivPM pc.2.2 l true) (pc.2.1 - pc.1) (2 * π * y) t).re| ≤
      (((List.range (D + 1)).foldr (fun l acc => acc +
        if wprev = 0 ∧ l % 2 = 0 then 0 else
        jumpTerm P YT l (if wprev = 0 then 0 else derivPM bprev l false) (if wprev = 0 then 1 else wprev)
          (derivPM pc.2.2 l true) (pc.2.1 - pc.1)) 0 : ℕ) : ℝ) / 2 ^ P := by
  have hω : 0 < 2 * π * y := by
    have := pi_bound hy
    have : (0 : ℝ) < 2 * (3141592 / 1000000) * (YT : ℝ) := by positivity
    linarith
  set ω := 2 * π * y with hωdef
  have hw2 : 0 < pc.2.1 - pc.1 := by omega
  -- the difference as one sum over l
  set S1 : ℕ → ℤ := fun l => if wprev = 0 then 0 else derivPM bprev l false with hS1
  set w1 : ℕ := if wprev = 0 then 1 else wprev with hw1
  have hw1p : 0 < w1 := by rw [hw1]; split_ifs with h <;> omega
  have hdiff : pendA P D wprev bprev ω t - knotA P D (fun l => derivPM pc.2.2 l true) (pc.2.1 - pc.1) ω t =
      ∑ l ∈ range (D + 1), (-1 : ℂ) ^ l * ((((S1 l : ℤ) : ℝ) / 2 ^ P * ((20000 : ℝ) / w1) ^ l -
        ((derivPM pc.2.2 l true : ℤ) : ℝ) / 2 ^ P * ((20000 : ℝ) / (pc.2.1 - pc.1 : ℕ)) ^ l : ℝ) : ℂ) *
        Complex.exp (((ω * t : ℝ) : ℂ) * I) / ((ω : ℂ) * I) ^ (l + 1) := by
    unfold pendA knotA
    split_ifs with h0
    · rw [zero_sub, ← sum_neg_distrib]
      refine sum_congr rfl (fun l _ => ?_)
      simp only [hS1, hw1, h0, if_true, Int.cast_zero, zero_div, zero_mul, zero_sub, Complex.ofReal_neg]
      ring
    · rw [← sum_sub_distrib]
      refine sum_congr rfl (fun l _ => ?_)
      simp only [hS1, hw1, h0, if_false]
      push_cast
      ring
  rw [hdiff, Complex.re_sum]
  -- bound term by term
  have hfold : ∀ (f : ℕ → ℕ), (((List.range (D + 1)).foldr (fun l acc => acc + f l) 0 : ℕ) : ℝ) =
      ∑ l ∈ range (D + 1), (f l : ℝ) := by
    intro f
    rw [← listSum_range]
    induction (List.range (D + 1)) with
    | nil => simp
    | cons a L ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih]; ring
  rw [hfold, sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun l _ => ?_))
  by_cases hl : wprev = 0 ∧ l % 2 = 0
  · rw [if_pos hl, ht hl.1, re_term_zero_even _ hl.2, abs_zero]; simp
  · rw [if_neg hl]
    refine (abs_re_term_le hω _ t l).trans ?_
    exact jumpTerm_bound (P := P) hYT hy l (S1 l) w1 (derivPM pc.2.2 l true) (pc.2.1 - pc.1) hw1p hw2

/-- The sum over the chain, regrouped at the knots. -/
theorem chain_regroup {D YT : ℕ} (hYT : 0 < YT) {y : ℝ} (hy : (YT : ℝ) ≤ y) :
    ∀ (L : List PPiece) (a : ℕ) (w : ℕ) (x : ℤ) (bs : List ℤ), chainOK a L = true → (∀ pc ∈ L, pc.1 < pc.2.1) →
      (w = 0 → a = 0) →
      |(pendA P D w bs (2 * π * y) ((a : ℝ) / 10000) +
          (L.map fun pc => pieceA P D pc (2 * π * y) (phi' pc) - pieceA P D pc (2 * π * y) (plo pc)).sum).re| ≤
        (jumpsAll P YT D (w, x, bs) L : ℝ) / 2 ^ P +
          |(match L.getLast? with
            | some pc => pieceA P D pc (2 * π * y) (phi' pc)
            | none => pendA P D w bs (2 * π * y) ((a : ℝ) / 10000)).re|
  | [], a, w, x, bs, _, _, _ => by simp [jumpsAll]
  | pc :: L, a, w, x, bs, hch, hord, hst => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hch
    obtain ⟨h1, h2⟩ := hch
    have hlt := hord pc (by simp)
    have ih := chain_regroup (D := D) hYT hy L pc.2.1 (pc.2.1 - pc.1) 0 pc.2.2 h2
      (fun q hq => hord q (by simp [hq])) (fun h => by omega)
    have hknot := knot_bound (P := P) (D := D) hYT hy w bs pc hlt (t := (a : ℝ) / 10000)
      (fun h => by rw [hst h]; simp)
    have hpend : pendA P D (pc.2.1 - pc.1) pc.2.2 (2 * π * y) ((pc.2.1 : ℕ) / 10000 : ℝ) =
        pieceA P D pc (2 * π * y) (phi' pc) := by
      unfold pendA
      rw [if_neg (by omega), pieceA_hi hlt]
      rfl
    have hlo : pieceA P D pc (2 * π * y) (plo pc) =
        knotA P D (fun l => derivPM pc.2.2 l true) (pc.2.1 - pc.1) (2 * π * y) ((a : ℝ) / 10000) := by
      rw [pieceA_lo hlt]; unfold plo; rw [h1]
    rw [hpend] at ih
    have hlast : (match (pc :: L).getLast? with
        | some q => pieceA P D q (2 * π * y) (phi' q)
        | none => pendA P D w bs (2 * π * y) ((a : ℝ) / 10000)) =
        (match L.getLast? with
        | some q => pieceA P D q (2 * π * y) (phi' q)
        | none => pieceA P D pc (2 * π * y) (phi' pc)) := by
      cases L with
      | nil => simp
      | cons q L' =>
        rw [List.getLast?_cons_cons]
        rcases h : (q :: L').getLast? with _ | z
        · simp at h
        · rfl
    rw [hlast]
    simp only [List.map_cons, List.sum_cons, jumpsAll, Nat.cast_add, add_div]
    have e : pendA P D w bs (2 * π * y) ((a : ℝ) / 10000) +
        (pieceA P D pc (2 * π * y) (phi' pc) - pieceA P D pc (2 * π * y) (plo pc) +
          (L.map fun pc => pieceA P D pc (2 * π * y) (phi' pc) - pieceA P D pc (2 * π * y) (plo pc)).sum) =
        (pendA P D w bs (2 * π * y) ((a : ℝ) / 10000) - pieceA P D pc (2 * π * y) (plo pc)) +
        (pieceA P D pc (2 * π * y) (phi' pc) +
          (L.map fun pc => pieceA P D pc (2 * π * y) (phi' pc) - pieceA P D pc (2 * π * y) (plo pc)).sum) := by ring
    rw [e, Complex.add_re]
    rw [hlo]
    have := abs_add_le (pendA P D w bs (2 * π * y) ((a : ℝ) / 10000) -
        knotA P D (fun l => derivPM pc.2.2 l true) (pc.2.1 - pc.1) (2 * π * y) ((a : ℝ) / 10000)).re
      (pieceA P D pc (2 * π * y) (phi' pc) +
          (L.map fun pc => pieceA P D pc (2 * π * y) (phi' pc) - pieceA P D pc (2 * π * y) (plo pc)).sum).re
    linarith

/-- The right end `r`. -/
theorem end_bound {D YT : ℕ} (hYT : 0 < YT) {y : ℝ} (hy : (YT : ℝ) ≤ y) (ps : List PPiece)
    (hord : ∀ pc ∈ ps, pc.1 < pc.2.1) :
    |(match ps.getLast? with
      | some pc => pieceA P D pc (2 * π * y) (phi' pc)
      | none => (0 : ℂ)).re| ≤ (jumpsEnd P YT D ps : ℝ) / 2 ^ P := by
  unfold jumpsEnd
  rcases hL : ps.getLast? with _ | pc
  · simp
  · simp only
    have hpc : pc ∈ ps := List.mem_of_getLast? hL
    have hlt := hord pc hpc
    have hω : 0 < 2 * π * y := by
      have := pi_bound hy
      have : (0 : ℝ) < 2 * (3141592 / 1000000) * (YT : ℝ) := by positivity
      linarith
    rw [pieceA_hi hlt]
    unfold knotA
    rw [Complex.re_sum]
    have hfold : ∀ (f : ℕ → ℕ), (((List.range (D + 1)).foldr (fun l acc => acc + f l) 0 : ℕ) : ℝ) =
        ∑ l ∈ range (D + 1), (f l : ℝ) := by
      intro f
      rw [← listSum_range]
      induction (List.range (D + 1)) with
      | nil => simp
      | cons a L ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih]; ring
    rw [hfold, sum_div]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun l _ => ?_))
    refine (abs_re_term_le hω _ _ l).trans ?_
    have := jumpTerm_bound (P := P) hYT hy l (derivPM pc.2.2 l false) (pc.2.1 - pc.1) 0 1 (by omega) one_pos
    simp only [Int.cast_zero, zero_div, zero_mul, sub_zero, Nat.cast_one, div_one] at this
    exact this

theorem re_listSum {α : Type*} (L : List α) (f : α → ℂ) : (L.map f).sum.re = (L.map fun x => (f x).re).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-- `|P̂(y)| ≤ 2 (jumpsAll + jumpsEnd) / 2^P` for `y ≥ Y`. -/
theorem phat_tail {D YT : ℕ} (hYT : 0 < YT) {ps : List PPiece} (hch : chainOK 0 ps = true)
    (hord : ∀ pc ∈ ps, pc.1 < pc.2.1) (hlen : ∀ pc ∈ ps, pc.2.2.length = D + 1) {y : ℝ} (hy : (YT : ℝ) ≤ y) :
    |PhatS P ps y| ≤ 2 * (((jumpsAll P YT D (0, 0, []) ps + jumpsEnd P YT D ps : ℕ) : ℝ) / 2 ^ P) := by
  have hω : 2 * π * y ≠ 0 := by
    have := pi_bound hy
    have : (0 : ℝ) < 2 * (3141592 / 1000000) * (YT : ℝ) := by positivity
    linarith
  have hsum : PhatS P ps y = 2 * ((ps.map fun pc => pieceA P D pc (2 * π * y) (phi' pc) -
      pieceA P D pc (2 * π * y) (plo pc)).sum).re := by
    unfold PhatS
    rw [re_listSum, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left (fun pc hpc => ?_)
    have := piece_ibp (P := P) (hord pc hpc) (hlen pc hpc) hω
    rw [← this]
  have hreg := chain_regroup (P := P) (D := D) hYT hy ps 0 0 0 [] hch hord (fun _ => rfl)
  have hpend0 : pendA P D 0 [] (2 * π * y) (((0 : ℕ) : ℝ) / 10000) = 0 := by simp [pendA]
  rw [hpend0, zero_add] at hreg
  have hend := end_bound (P := P) (D := D) hYT hy ps hord
  rw [hsum, abs_mul, abs_two]
  push_cast
  rw [add_div]
  linarith

end SignUnc.Chk
