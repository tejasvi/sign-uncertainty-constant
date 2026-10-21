import SignUnc.LowSound4

/-!
# Soundness of the lower checker, part 5: `P̂` in `y` (`phatJet`, `phatRem`), pieces and segments in `y`

`P̂(y₀ + s) = Σ_{j ≤ M} HJ_j(y₀) s^j + E` with `|E| ≤ 2r Pmax (2πr|s|)^{M+1}/(M+1)!` (the Taylor bound of `e^{ix}`
pointwise under the integral, no differentiation under the integral sign).  `HJ_j(y₀)` from the per-piece moments
`μ_{j,n} = ∫ p(σ) (c + ησ)^j σ^n dσ`, the series of `e^{iκσ}` truncated after `N` terms.  `lsegOK_sound`:
`1 - v + P̂ > m + 2rε` on every segment.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Complex Finset MeasureTheory intervalIntegral

variable {P : ℕ}

/-! ## The jets of `P̂` -/

/-- The `j`-th normalized `y`-jet of `cos(2πyt)`: `(2πt)^j Re(e^{2πiyt} i^j / j!)`. -/
noncomputable def jt (j : ℕ) (y t : ℝ) : ℝ :=
  (2 * π * t) ^ j * (Complex.exp (((2 * π * y * t : ℝ) : ℂ) * I) * I ^ j / (j.factorial : ℂ)).re

/-- `HJ_j(y) = Σ_k 2 ∫_{lo_k}^{hi_k} P_k(t) jt_j(y, t) dt`. -/
noncomputable def HJ (P : ℕ) (ps : List PPiece) (j : ℕ) (y : ℝ) : ℝ :=
  (ps.map fun pc => 2 * ∫ t in plo pc..phi' pc, Peval P pc t * jt j y t).sum

theorem continuous_jt (j : ℕ) (y : ℝ) : Continuous (jt j y) := by
  unfold jt; fun_prop

theorem Peval_eq_pR (pc : PPiece) (t : ℝ) : Peval P pc t = pR P pc ((t - pcR pc) / peR pc) := by
  unfold Peval pR
  rw [peval_eq_sum, sum_div]
  refine sum_congr rfl (fun i _ => ?_)
  unfold pcR peR; ring

theorem abs_Peval_le {pc : PPiece} (hlt : pc.1 < pc.2.1) {t : ℝ} (ht : t ∈ Set.Icc (plo pc) (phi' pc)) :
    |Peval P pc t| ≤ (pmaxOne pc : ℝ) / 2 ^ P := by
  rw [Peval_eq_pR]
  apply abs_pR_le
  have he := peR_pos hlt
  rw [abs_div, abs_of_pos he, div_le_one he, abs_le]
  rw [plo_eq hlt.le, phi_eq hlt.le] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem phi_sub_plo {pc : PPiece} (h : pc.1 ≤ pc.2.1) : phi' pc - plo pc = 2 * peR pc := by
  rw [plo_eq h, phi_eq h]; ring

theorem piece_t_range {pc : PPiece} (hle : pc.1 ≤ pc.2.1) (hhi : pc.2.1 ≤ 5502) {t : ℝ}
    (ht : t ∈ Set.Icc (plo pc) (phi' pc)) : 0 ≤ t ∧ t ≤ 5502 / 10000 := by
  have h0 : 0 ≤ plo pc := by unfold plo; positivity
  have h1 : phi' pc ≤ 5502 / 10000 := by
    unfold phi'
    have : ((pc.2.1 : ℕ) : ℝ) ≤ 5502 := by exact_mod_cast hhi
    linarith
  exact ⟨h0.trans ht.1, ht.2.trans h1⟩

/-- The pointwise Taylor bound of `cos(2π(y₀ + s)t)` in `s`. -/
theorem jt_taylor (y0 s t : ℝ) (M : ℕ) :
    |Real.cos (2 * π * (y0 + s) * t) - ∑ j ∈ range (M + 1), jt j y0 t * s ^ j| ≤
      |2 * π * t * s| ^ (M + 1) / ((M + 1).factorial : ℝ) := by
  have hK : ‖Complex.exp (((2 * π * y0 * t : ℝ) : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have h := taylor_expI_part _ hK (M + 1) (2 * π * t * s)
  have e1 : (Complex.exp (((2 * π * y0 * t : ℝ) : ℂ) * I) * Complex.exp (((2 * π * t * s : ℝ) : ℂ) * I)).re =
      Real.cos (2 * π * (y0 + s) * t) := by
    rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.exp_ofReal_mul_I_re]
    congr 1; ring
  have e2 : ∑ j ∈ range (M + 1), (Complex.exp (((2 * π * y0 * t : ℝ) : ℂ) * I) * I ^ j / (j.factorial : ℂ)).re *
      (2 * π * t * s) ^ j = ∑ j ∈ range (M + 1), jt j y0 t * s ^ j := by
    refine sum_congr rfl (fun j _ => ?_)
    unfold jt; rw [mul_pow]; ring
  rw [e1, e2] at h; exact h

theorem piece_sum_integral (pc : PPiece) (y0 s : ℝ) (M : ℕ) :
    ∑ j ∈ range (M + 1), 2 * (∫ t in plo pc..phi' pc, Peval P pc t * jt j y0 t) * s ^ j =
      2 * ∫ t in plo pc..phi' pc, Peval P pc t * ∑ j ∈ range (M + 1), jt j y0 t * s ^ j := by
  have hc := continuous_Peval (P := P) pc
  have hfun : (fun t => Peval P pc t * ∑ j ∈ range (M + 1), jt j y0 t * s ^ j) =
      fun t => ∑ j ∈ range (M + 1), Peval P pc t * jt j y0 t * s ^ j := by
    funext t; rw [mul_sum]; refine sum_congr rfl (fun j _ => ?_); ring
  rw [hfun, intervalIntegral.integral_finsetSum (fun j _ => by
    have := continuous_jt j y0
    exact (by fun_prop : Continuous fun t => Peval P pc t * jt j y0 t * s ^ j).intervalIntegrable _ _), mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [intervalIntegral.integral_mul_const]; ring

/-- `|P̂(y₀ + s) - Σ_{j ≤ M} HJ_j(y₀) s^j| ≤ 2r Pmax (2πr|s|)^{M+1}/(M+1)!`. -/
theorem phat_taylor {ps : List PPiece} (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1)
    (y0 s : ℝ) (M : ℕ) :
    |PhatS P ps (y0 + s) - ∑ j ∈ range (M + 1), HJ P ps j y0 * s ^ j| ≤
      2 * (5502 / 10000) * ((pmaxHi ps : ℝ) / 2 ^ P) *
        ((2 * π * (5502 / 10000) * |s|) ^ (M + 1) / ((M + 1).factorial : ℝ)) := by
  set B := (2 * π * (5502 / 10000) * |s|) ^ (M + 1) / ((M + 1).factorial : ℝ) with hB
  have hB0 : 0 ≤ B := by positivity
  have hbnd := chain_bounds 0 ps hch hord
  have e1 : ∑ j ∈ range (M + 1), HJ P ps j y0 * s ^ j =
      (ps.map fun pc => 2 * ∫ t in plo pc..phi' pc, Peval P pc t * ∑ j ∈ range (M + 1), jt j y0 t * s ^ j).sum := by
    unfold HJ
    simp only [← List.sum_map_mul_right]
    rw [sum_range_listSum]
    congr 1
    refine List.map_congr_left (fun pc _ => ?_)
    exact piece_sum_integral pc y0 s M
  rw [e1, PhatS]
  refine (abs_listSum_sub_le _ _ ps).trans ?_
  refine (listSum_le_listSum ps (g := fun pc => 2 * peR pc * (2 * ((pmaxHi ps : ℝ) / 2 ^ P * B)))
    (fun pc hpc => ?_)).trans (le_of_eq ?_)
  · have hlt := hord pc hpc
    have hc := continuous_Peval (P := P) pc
    have hsc : Continuous fun t => ∑ j ∈ range (M + 1), jt j y0 t * s ^ j := by
      have := fun j => continuous_jt j y0
      fun_prop
    rw [← mul_sub, ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t => Peval P pc t * Real.cos (2 * π * (y0 + s) * t)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => Peval P pc t * ∑ j ∈ range (M + 1), jt j y0 t * s ^ j).intervalIntegrable _ _)]
    have hbd : ∀ t ∈ Set.uIoc (plo pc) (phi' pc), ‖Peval P pc t * Real.cos (2 * π * (y0 + s) * t) -
        Peval P pc t * ∑ j ∈ range (M + 1), jt j y0 t * s ^ j‖ ≤ (pmaxHi ps : ℝ) / 2 ^ P * B := by
      intro t ht
      have hle : plo pc ≤ phi' pc := by linarith [phi_sub_plo hlt.le, peR_pos hlt]
      rw [Set.uIoc_of_le hle] at ht
      have ht' : t ∈ Set.Icc (plo pc) (phi' pc) := ⟨ht.1.le, ht.2⟩
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      have h1 : |Peval P pc t| ≤ (pmaxHi ps : ℝ) / 2 ^ P := by
        refine (abs_Peval_le hlt ht').trans ?_
        have : (pmaxOne pc : ℝ) ≤ pmaxHi ps := by exact_mod_cast pmaxOne_le_pmaxHi ps pc hpc
        exact div_le_div_of_nonneg_right this (by positivity)
      have htr := piece_t_range hlt.le (hbnd pc hpc).2 ht'
      have h2 := jt_taylor y0 s t M
      have h3 : |2 * π * t * s| ^ (M + 1) / ((M + 1).factorial : ℝ) ≤ B := by
        rw [hB]
        refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ?_ _) (by positivity)
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_nonneg htr.1]
        have h2p : 0 < 2 * π := by positivity
        have := mul_le_mul_of_nonneg_left htr.2 h2p.le
        exact mul_le_mul_of_nonneg_right this (abs_nonneg s)
      exact mul_le_mul h1 (h2.trans h3) (abs_nonneg _) (by positivity)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [phi_sub_plo hlt.le, peR_pos hlt] :
      (0 : ℝ) ≤ phi' pc - plo pc), phi_sub_plo hlt.le] at this
    rw [abs_mul, abs_two]
    calc 2 * |∫ t in plo pc..phi' pc, (Peval P pc t * Real.cos (2 * π * (y0 + s) * t) -
          Peval P pc t * ∑ j ∈ range (M + 1), jt j y0 t * s ^ j)| ≤
        2 * ((pmaxHi ps : ℝ) / 2 ^ P * B * (2 * peR pc)) := by linarith
      _ = _ := by ring
  · rw [List.sum_map_mul_right, chain_width_sum 0 ps hch hord]
    push_cast; ring

/-! ## The series `Σ_n i^n κ^n/n! μ_n` in balls -/

/-- `Σ_l i^(n+l) x^(n+l)/(n+l)! m_l`. -/
noncomputable def serC (x : ℝ) : ℕ → List ℝ → ℂ
  | _, [] => 0
  | n, m :: ms => I ^ n * ((x ^ n / (n.factorial : ℝ) * m : ℝ) : ℂ) + serC x (n + 1) ms

theorem serC_eq (x : ℝ) : ∀ (n : ℕ) (ms : List ℝ), serC x n ms =
    ∑ l ∈ range ms.length, I ^ (n + l) * ((x ^ (n + l) / ((n + l).factorial : ℝ) * ms.getD l 0 : ℝ) : ℂ)
  | n, [] => by simp [serC]
  | n, m :: ms => by
    rw [serC, serC_eq x (n + 1) ms, List.length_cons, sum_range_succ']
    simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]; congr 1
    refine sum_congr rfl (fun l _ => ?_)
    rw [show n + (l + 1) = n + 1 + l by ring]

/-- `Σ_{n<N} i^n κ^n/n! f_n`. -/
noncomputable def serS (κ : ℝ) (N : ℕ) (f : ℕ → ℝ) : ℂ :=
  ∑ n ∈ range N, I ^ n * ((κ ^ n / (n.factorial : ℝ) * f n : ℝ) : ℂ)

theorem serC_range (x : ℝ) (f : ℕ → ℝ) (N : ℕ) : serC x 0 ((List.range N).map f) = serS x N f := by
  rw [serC_eq, List.length_map, List.length_range, serS]
  refine sum_congr rfl (fun l hl => ?_)
  rw [zero_add, List.getD_eq_getElem _ _ (by simpa using List.mem_range.mp hl), List.getElem_map, List.getElem_range]

theorem I_pow_mod4 (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
  have : I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  rw [this, one_pow, one_mul]

theorem mem_seriesIA {x : ℝ} {X : Ball} (hx : mem P x X) :
    ∀ (n : ℕ) {a : Ball} {ms : List ℝ} {Ms : List Ball}, mem P (x ^ n / (n.factorial : ℝ)) a → MemL P ms Ms →
      mem P (serC x n ms).re (seriesIA P X n a Ms).1 ∧ mem P (serC x n ms).im (seriesIA P X n a Ms).2
  | n, a, [], [], _, List.Forall₂.nil => by
    simp only [serC, seriesIA, Complex.zero_re, Complex.zero_im]
    exact ⟨mem_zero_ball, mem_zero_ball⟩
  | n, a, m :: ms, b :: Ms, ha, List.Forall₂.cons hm h => by
    have ha' : mem P (x ^ (n + 1) / ((n + 1).factorial : ℝ)) (divNat (n + 1) (mul P a X)) := by
      have := mem_divNat (d := n + 1) (by omega) (mem_mul ha hx)
      convert this using 1
      rw [Nat.factorial_succ]; push_cast
      have h0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      field_simp; ring
    obtain ⟨ih1, ih2⟩ := mem_seriesIA hx (n + 1) ha' h
    have ht := mem_mul ha hm
    simp only [seriesIA, serC]
    rw [I_pow_mod4]
    have hI3 : I ^ 3 = -I := by rw [pow_three, Complex.I_mul_I, mul_neg_one]
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h4 | h4 | h4 | h4 <;>
      simp only [h4]
    · refine ⟨?_, ?_⟩
      · convert mem_add ht ih1 using 1
        simp only [pow_zero, one_mul, Complex.add_re, Complex.ofReal_re]
      · convert ih2 using 1
        simp only [pow_zero, one_mul, Complex.add_im, Complex.ofReal_im, zero_add]
    · refine ⟨?_, ?_⟩
      · convert ih1 using 1
        simp only [pow_one, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      · convert mem_add ht ih2 using 1
        simp only [pow_one, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
    · refine ⟨?_, ?_⟩
      · convert mem_sub ih1 ht using 1
        simp only [Complex.I_sq, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.one_re,
          Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      · convert ih2 using 1
        simp only [Complex.I_sq, Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
          Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
    · refine ⟨?_, ?_⟩
      · convert ih1 using 1
        simp only [hI3, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      · convert mem_sub ih2 ht using 1
        simp only [hI3, Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring

theorem mem_UV {θ : ℝ} {z : ℂ} {cs : Ball × Ball} (hcs : mem P (Real.cos θ) cs.1 ∧ mem P (Real.sin θ) cs.2)
    {XY : Ball × Ball} (hXY : mem P z.re XY.1 ∧ mem P z.im XY.2) :
    mem P (Complex.exp ((θ : ℂ) * I) * z).re (sub (mul P cs.1 XY.1) (mul P cs.2 XY.2)) ∧
    mem P (Complex.exp ((θ : ℂ) * I) * z).im (add (mul P cs.2 XY.1) (mul P cs.1 XY.2)) := by
  constructor
  · rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    exact mem_sub (mem_mul hcs.1 hXY.1) (mem_mul hcs.2 hXY.2)
  · rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    convert mem_add (mem_mul hcs.2 hXY.1) (mem_mul hcs.1 hXY.2) using 1; ring

theorem mem_widen_err {x v : ℝ} {B : Ball} {err : ℕ} (hv : mem P v B) (hx : |x - v| ≤ (err : ℝ) / 2 ^ P) :
    mem P x (⟨B.m, B.r + err⟩ : Ball) := by
  unfold mem at hv ⊢
  calc |x - (B.m : ℝ) / 2 ^ P| ≤ |x - v| + |v - (B.m : ℝ) / 2 ^ P| := abs_sub_le _ _ _
    _ ≤ (err : ℝ) / 2 ^ P + (B.r : ℝ) / 2 ^ P := add_le_add hx hv
    _ = ((B.r + err : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

/-! ## One entry of `phatJet` -/

/-- The per-piece moments `μ_{j,n} = ∫_{-1}^{1} p(σ) (c + ησ)^j σ^n dσ`. -/
noncomputable def muJ (P : ℕ) (pc : PPiece) (j n : ℕ) : ℝ :=
  ∫ σ in (-1 : ℝ)..1, pR P pc σ * (pcR pc + peR pc * σ) ^ j * σ ^ n

theorem re_div_natCast (z : ℂ) (n : ℕ) : (z / (n : ℂ)).re = z.re / n := by
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]

/-- The analytic part of one entry: the truncated series against the true jet of a piece. -/
theorem phat_entry {pc : PPiece} (hlt : pc.1 < pc.2.1) (hhi : pc.2.1 ≤ 5502) (y : ℝ) (j N : ℕ) :
    |2 * (∫ t in plo pc..phi' pc, Peval P pc t * jt j y t) -
      2 * ((2 * π) ^ j / (j.factorial : ℝ) * (peR pc * (I ^ j * (Complex.exp ((((2 * π * (y * pcR pc)) : ℝ) : ℂ) * I) *
        serS (2 * π * y * peR pc) N (muJ P pc j))).re))| ≤
    2 * ((2 * π) ^ j / (j.factorial : ℝ) * (peR pc * (2 * ((pmaxOne pc : ℝ) / 2 ^ P *
      ((5502 / 10000) ^ j * (|2 * π * y * peR pc| ^ N / (N.factorial : ℝ))))))) := by
  have he := peR_pos hlt
  have hpc := continuous_pR (P := P) pc
  set c := pcR pc with hc
  set η := peR pc with hη
  set κ := 2 * π * y * η with hκ
  set A := (2 * π) ^ j / (j.factorial : ℝ) with hA
  set K : ℂ := I ^ j * Complex.exp ((((2 * π * (y * c)) : ℝ) : ℂ) * I) with hK
  have hKn : ‖K‖ = 1 := by rw [hK, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_exp_ofReal_mul_I]
  have hA0 : 0 ≤ A := by positivity
  -- the true jet in σ
  have hjt : ∀ σ, jt j y (η * σ + c) = A * ((c + η * σ) ^ j * (K * Complex.exp (((κ * σ : ℝ) : ℂ) * I)).re) := by
    intro σ
    unfold jt
    have e0 : (2 * π * y * (η * σ + c) : ℝ) = 2 * π * (y * c) + κ * σ := by rw [hκ]; ring
    have e1 : Complex.exp (((2 * π * y * (η * σ + c) : ℝ) : ℂ) * I) * I ^ j =
        K * Complex.exp (((κ * σ : ℝ) : ℂ) * I) := by
      rw [e0, Complex.ofReal_add, add_mul, Complex.exp_add, hK]
      ring
    rw [e1, re_div_natCast, hA, mul_pow]
    ring
  rw [integral_piece hlt, ← hc, ← hη]
  simp only [hjt]
  -- the series as an integral
  have hser : (K * serS κ N (muJ P pc j)).re =
      ∫ σ in (-1 : ℝ)..1, pR P pc σ * ((c + η * σ) ^ j *
        ∑ n ∈ range N, (K * I ^ n / (n.factorial : ℂ)).re * (κ * σ) ^ n) := by
    have hfun : (fun σ => pR P pc σ * ((c + η * σ) ^ j * ∑ n ∈ range N, (K * I ^ n / (n.factorial : ℂ)).re * (κ * σ) ^ n)) =
        fun σ => ∑ n ∈ range N, ((K * I ^ n / (n.factorial : ℂ)).re * κ ^ n) *
          (pR P pc σ * (c + η * σ) ^ j * σ ^ n) := by
      funext σ; rw [mul_sum, mul_sum]; refine sum_congr rfl (fun n _ => ?_); rw [mul_pow]; ring
    rw [hfun, intervalIntegral.integral_finsetSum (fun n _ => (by fun_prop : Continuous fun σ =>
      ((K * I ^ n / (n.factorial : ℂ)).re * κ ^ n) * (pR P pc σ * (c + η * σ) ^ j * σ ^ n)).intervalIntegrable _ _)]
    rw [serS, mul_sum, Complex.re_sum]
    refine sum_congr rfl (fun n _ => ?_)
    rw [intervalIntegral.integral_const_mul,
      show (∫ σ in (-1 : ℝ)..1, pR P pc σ * (c + η * σ) ^ j * σ ^ n) = muJ P pc j n from rfl,
      ← mul_assoc, Complex.re_mul_ofReal, re_div_natCast]
    ring
  have hKeq : I ^ j * (Complex.exp ((((2 * π * (y * c)) : ℝ) : ℂ) * I) * serS κ N (muJ P pc j)) =
      K * serS κ N (muJ P pc j) := by rw [hK]; exact (mul_assoc _ _ _).symm
  rw [hKeq, hser]
  -- the difference
  have hfA : (fun σ => pR P pc σ * (A * ((c + η * σ) ^ j * (K * Complex.exp (((κ * σ : ℝ) : ℂ) * I)).re))) =
      fun σ => A * (pR P pc σ * ((c + η * σ) ^ j * (K * Complex.exp (((κ * σ : ℝ) : ℂ) * I)).re)) := by
    funext σ; ring
  rw [hfA, intervalIntegral.integral_const_mul]
  have hc1 : Continuous fun σ => pR P pc σ * ((c + η * σ) ^ j * (K * Complex.exp (((κ * σ : ℝ) : ℂ) * I)).re) := by
    fun_prop
  have hc2 : Continuous fun σ => pR P pc σ * ((c + η * σ) ^ j *
      ∑ n ∈ range N, (K * I ^ n / (n.factorial : ℂ)).re * (κ * σ) ^ n) := by fun_prop
  have hdiff : 2 * (η * (A * ∫ σ in (-1 : ℝ)..1, pR P pc σ * ((c + η * σ) ^ j *
        (K * Complex.exp (((κ * σ : ℝ) : ℂ) * I)).re))) -
      2 * (A * (η * ∫ σ in (-1 : ℝ)..1, pR P pc σ * ((c + η * σ) ^ j *
        ∑ n ∈ range N, (K * I ^ n / (n.factorial : ℂ)).re * (κ * σ) ^ n))) =
      2 * (A * (η * ∫ σ in (-1 : ℝ)..1, (pR P pc σ * ((c + η * σ) ^ j *
        (K * Complex.exp (((κ * σ : ℝ) : ℂ) * I)).re) - pR P pc σ * ((c + η * σ) ^ j *
        ∑ n ∈ range N, (K * I ^ n / (n.factorial : ℂ)).re * (κ * σ) ^ n)))) := by
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]; ring
  rw [hdiff]
  have hbd : ∀ σ ∈ Set.uIoc (-1 : ℝ) 1, ‖pR P pc σ * ((c + η * σ) ^ j * (K * Complex.exp (((κ * σ : ℝ) : ℂ) * I)).re) -
      pR P pc σ * ((c + η * σ) ^ j * ∑ n ∈ range N, (K * I ^ n / (n.factorial : ℂ)).re * (κ * σ) ^ n)‖ ≤
      (pmaxOne pc : ℝ) / 2 ^ P * ((5502 / 10000) ^ j * (|κ| ^ N / (N.factorial : ℝ))) := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num)] at hσ
    have hσ1 : |σ| ≤ 1 := abs_le.mpr ⟨hσ.1.le, hσ.2⟩
    rw [Real.norm_eq_abs, ← mul_sub, ← mul_sub, abs_mul, abs_mul]
    have h1 := abs_pR_le (P := P) pc hσ1
    have hTb : 0 ≤ c + η * σ ∧ c + η * σ ≤ 5502 / 10000 := piece_t_bounds hlt.le hhi hσ1
    have h2 : |(c + η * σ) ^ j| ≤ (5502 / 10000) ^ j := by
      rw [abs_pow, abs_of_nonneg hTb.1]; exact pow_le_pow_left₀ hTb.1 hTb.2 j
    have h3 := taylor_expI_part K hKn N (κ * σ)
    have h4 : |κ * σ| ^ N / (N.factorial : ℝ) ≤ |κ| ^ N / (N.factorial : ℝ) := by
      refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ?_ _) (by positivity)
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hσ1
    have h5 := h3.trans h4
    exact mul_le_mul h1 (mul_le_mul h2 h5 (abs_nonneg _) (by positivity)) (by positivity) (by positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, show |(1 : ℝ) - -1| = 2 by norm_num] at this
  rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hA0, abs_of_pos he]
  have h6 : 0 ≤ A * η := by positivity
  have h7 := mul_le_mul_of_nonneg_left this h6
  linarith

theorem mem_two_pi (P : ℕ) : mem P (2 * π) (mulInt 2 (piB P)) := by
  have := mem_mulInt 2 (mem_piB P); simpa using this

theorem mem_r (P : ℕ) : mem P (5502 / 10000 : ℝ) (ofRat P 2751 5000) := by
  have := mem_ofRat P 2751 5000 (by norm_num)
  convert this using 1; norm_num

/-- One entry of `phatJet`, for any ball `base` containing `Re(i^j e^{iθ} S)`. -/
theorem mem_entry_of_base {pc : PPiece} (hlt : pc.1 < pc.2.1) (hhi : pc.2.1 ≤ 5502) (y : ℝ) {j N : ℕ}
    {base we : Ball}
    (hbase : mem P (I ^ j * (Complex.exp ((((2 * π * (y * pcR pc)) : ℝ) : ℂ) * I) *
      serS (2 * π * y * peR pc) N (muJ P pc j))).re base)
    (hwe : mem P (2 * π * y * peR pc) we) :
    mem P (2 * ∫ t in plo pc..phi' pc, Peval P pc t * jt j y t)
      (⟨(mulInt 2 (mul P (divNat (fact j) (powB P (mulInt 2 (piB P)) j)) (mul P (peta P pc) base))).m,
        (mulInt 2 (mul P (divNat (fact j) (powB P (mulInt 2 (piB P)) j)) (mul P (peta P pc) base))).r +
        (mul P (mulInt 4 (mul P (divNat (fact j) (powB P (mulInt 2 (piB P)) j))
            (mul P (peta P pc) ⟨(pmaxOne pc : Int), 0⟩)))
          (mul P (powB P (ofRat P 2751 5000) j)
            (divNat (fact N) (mulInt 2 (powB P ⟨(we.absHi : Int), 0⟩ N))))).absHi⟩ : Ball) := by
  have hfac : mem P ((2 * π) ^ j / (j.factorial : ℝ)) (divNat (fact j) (powB P (mulInt 2 (piB P)) j)) := by
    have := mem_divNat (d := fact j) (by rw [fact_eq]; positivity) (mem_powB (mem_two_pi P) j)
    rw [show ((fact j : ℕ) : ℝ) = (j.factorial : ℝ) by rw [fact_eq]] at this
    exact this
  have hval := mem_mulInt 2 (mem_mul hfac (mem_mul (mem_peta (P := P) pc) hbase))
  refine mem_widen_err hval ?_
  have hent := phat_entry (P := P) hlt hhi y j N
  have hwe' := abs_le_absHi hwe
  have herr := abs_le_absHi (mem_mul (mem_mulInt 4 (mem_mul hfac (mem_mul (mem_peta (P := P) pc)
      (mem_point P (pmaxOne pc : ℤ))))) (mem_mul (mem_powB (mem_r P) j)
      (mem_divNat (d := fact N) (by rw [fact_eq]; positivity) (mem_mulInt 2 (mem_powB (mem_point P (we.absHi : ℤ)) N)))))
  refine le_trans ?_ ((le_abs_self _).trans herr)
  have hη := peR_nonneg pc
  have hpm : (0 : ℝ) ≤ (pmaxOne pc : ℝ) / 2 ^ P := by positivity
  have hpow : |2 * π * y * peR pc| ^ N ≤ ((we.absHi : ℝ) / 2 ^ P) ^ N := pow_le_pow_left₀ (abs_nonneg _) hwe' N
  have hF : 0 ≤ (2 * π) ^ j / (j.factorial : ℝ) * peR pc * ((pmaxOne pc : ℝ) / 2 ^ P) * (5502 / 10000) ^ j /
      (N.factorial : ℝ) := by positivity
  calc _ ≤ 2 * ((2 * π) ^ j / (j.factorial : ℝ) * (peR pc * (2 * ((pmaxOne pc : ℝ) / 2 ^ P *
          ((5502 / 10000) ^ j * (|2 * π * y * peR pc| ^ N / (N.factorial : ℝ))))))) := hent
    _ = 4 * ((2 * π) ^ j / (j.factorial : ℝ) * peR pc * ((pmaxOne pc : ℝ) / 2 ^ P) * (5502 / 10000) ^ j /
          (N.factorial : ℝ)) * |2 * π * y * peR pc| ^ N := by ring
    _ ≤ 4 * ((2 * π) ^ j / (j.factorial : ℝ) * peR pc * ((pmaxOne pc : ℝ) / 2 ^ P) * (5502 / 10000) ^ j /
          (N.factorial : ℝ)) * (2 * ((we.absHi : ℝ) / 2 ^ P) ^ N) := by
        gcongr
        have : 0 ≤ ((we.absHi : ℝ) / 2 ^ P) ^ N := by positivity
        linarith
    _ = _ := by push_cast; rw [fact_eq]; ring

/-! ## `phatJet` -/

theorem memL_foldr_addL {α : Type*} (M : ℕ) (F : α → ℕ → ℝ) (T : α → Option (List Ball)) :
    ∀ (L : List α), (∀ x ∈ L, ∀ a, T x = some a → MemL P ((List.range (M + 1)).map (F x)) a) →
      ∀ {H : List Ball}, (L.map T).foldr (fun t acc => t.bind fun a => acc.bind fun b => some (addL a b))
        (some (zeroL (M + 1))) = some H →
      MemL P ((List.range (M + 1)).map fun j => (L.map fun x => F x j).sum) H
  | [], _, H, h => by
    simp only [List.map_nil, List.foldr_nil, Option.some.injEq] at h
    subst h
    have := memL_zeroL (P := P) (M + 1)
    simpa using this
  | x :: L, hT, H, h => by
    simp only [List.map_cons, List.foldr_cons, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    have h1 := hT x (by simp) a ha
    have h2 := memL_foldr_addL M F T L (fun y hy => hT y (by simp [hy])) hb
    have := memL_addL h1 h2
    rw [zipWith_add_range] at this
    simpa using this

theorem zip_map_map {α β γ : Type*} (f : α → β) (g : α → γ) :
    ∀ L : List α, L.zip ((L.map f).zip (L.map g)) = L.map fun a => (a, f a, g a)
  | [] => rfl
  | a :: L => by simp [zip_map_map f g L]

theorem memL_zipWith_range {β : Type*} {R : ℕ → β → Prop} {f : ℕ → β → Ball} {g : ℕ → ℝ}
    (hf : ∀ j b, R j b → mem P (g j) (f j b)) :
    ∀ {l : List ℕ} {bs : List β}, List.Forall₂ R l bs → MemL P (l.map g) (List.zipWith f l bs)
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => List.Forall₂.cons (hf _ _ h) (memL_zipWith_range hf t)

theorem memL_phatJet {n k M N : ℕ} {ps : List PPiece} (hord : ∀ pc ∈ ps, pc.1 < pc.2.1)
    (hbnd : ∀ pc ∈ ps, pc.2.1 ≤ 5502) {y0 : ℤ} {H : List Ball}
    (h : phatJet P n k M N ps (ps.map (pieceMoms P M N)) (ps.map pmaxOne) ⟨y0, 0⟩ = some H) :
    MemL P ((List.range (M + 1)).map fun j => HJ P ps j ((y0 : ℝ) / 2 ^ P)) H := by
  set y : ℝ := (y0 : ℝ) / 2 ^ P with hy
  unfold phatJet at h
  dsimp only at h
  rw [zip_map_map] at h
  have key := memL_foldr_addL (P := P) M (fun x j => 2 * ∫ t in plo x.1..phi' x.1, Peval P x.1 t * jt j y t) _
    (ps.map fun a => (a, pieceMoms P M N a, pmaxOne a)) ?_ h
  · convert key using 2
    funext j
    rw [HJ, List.map_map]
    rfl
  intro x hx a ha
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hx
  have hlt := hord pc hpc
  have hhi := hbnd pc hpc
  dsimp only at ha
  obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp ha
  have hcs' := mem_cosSinTurn (mem_mul (mem_point P y0) (mem_pcen (P := P) pc)) hcs
  have hwe : mem P (2 * π * y * peR pc) (mul P (mul P (mulInt 2 (piB P)) ⟨y0, 0⟩) (peta P pc)) :=
    mem_mul (mem_mul (mem_two_pi P) (mem_point P y0)) (mem_peta pc)
  refine memL_zipWith_range (R := fun j row => MemL P ((List.range N).map (muJ P pc j)) row) ?_
    (forall₂_pieceMoms M N pc)
  intro j mj hrow
  have hXY := mem_seriesIA hwe 0 (a := ofInt P 1) (by simpa using mem_ofInt P 1) hrow
  rw [serC_range] at hXY
  have hUV := mem_UV (θ := 2 * π * (y * pcR pc)) hcs' hXY
  set w : ℂ := Complex.exp ((((2 * π * (y * pcR pc)) : ℝ) : ℂ) * I) * serS (2 * π * y * peR pc) N (muJ P pc j) with hw
  have hIj := I_pow_mod4 j
  dsimp only
  rcases (by omega : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3) with h4 | h4 | h4 | h4 <;>
    simp only [h4] <;> refine mem_entry_of_base hlt hhi y ?_ hwe
  · rw [hIj, h4, pow_zero, one_mul]; exact hUV.1
  · rw [hIj, h4, pow_one, Complex.mul_re, Complex.I_re, Complex.I_im]
    convert mem_neg hUV.2 using 1; ring
  · rw [hIj, h4, Complex.I_sq, neg_one_mul, Complex.neg_re]
    exact mem_neg hUV.1
  · have hI3 : I ^ 3 = -I := by rw [pow_three, Complex.I_mul_I, mul_neg_one]
    rw [hIj, h4, hI3, neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    convert hUV.2 using 1; ring

/-! ## The remainder of `P̂` in `y` -/

theorem phatRem_bound {ps : List PPiece} {M pmax eta : ℕ} (hpm : pmaxHi ps ≤ pmax) {s : ℝ}
    (hs : |s| ≤ (eta : ℝ) / 2 ^ P) :
    2 * (5502 / 10000) * ((pmaxHi ps : ℝ) / 2 ^ P) *
      ((2 * π * (5502 / 10000) * |s|) ^ (M + 1) / ((M + 1).factorial : ℝ)) ≤ (phatRem P M pmax eta : ℝ) / 2 ^ P := by
  unfold phatRem
  have h := abs_le_absHi (mem_mul (mem_mul (mem_mulInt 4 (mem_r P)) (mem_point P (pmax : ℤ)))
    (mem_divNat (d := fact (M + 1)) (by rw [fact_eq]; positivity)
      (mem_powB (mem_mul (mem_mul (mem_two_pi P) (mem_r P)) (mem_point P (eta : ℤ))) (M + 1))))
  refine le_trans ?_ ((le_abs_self _).trans h)
  push_cast
  rw [fact_eq]
  have hpm' : (pmaxHi ps : ℝ) / 2 ^ P ≤ (pmax : ℝ) / 2 ^ P :=
    div_le_div_of_nonneg_right (by exact_mod_cast hpm) (by positivity)
  have hpow : (2 * π * (5502 / 10000) * |s|) ^ (M + 1) ≤ (2 * π * (5502 / 10000) * ((eta : ℝ) / 2 ^ P)) ^ (M + 1) := by
    gcongr
  have h0 : 0 ≤ (2 * π * (5502 / 10000) * |s|) ^ (M + 1) / ((M + 1).factorial : ℝ) := by positivity
  have h1 : (2 * π * (5502 / 10000) * |s|) ^ (M + 1) / ((M + 1).factorial : ℝ) ≤
      (2 * π * (5502 / 10000) * ((eta : ℝ) / 2 ^ P)) ^ (M + 1) / ((M + 1).factorial : ℝ) :=
    div_le_div_of_nonneg_right hpow (by positivity)
  have h2 : 0 ≤ (pmaxHi ps : ℝ) / 2 ^ P := by positivity
  calc 2 * (5502 / 10000) * ((pmaxHi ps : ℝ) / 2 ^ P) *
        ((2 * π * (5502 / 10000) * |s|) ^ (M + 1) / ((M + 1).factorial : ℝ))
      ≤ 2 * (5502 / 10000) * ((pmax : ℝ) / 2 ^ P) *
        ((2 * π * (5502 / 10000) * ((eta : ℝ) / 2 ^ P)) ^ (M + 1) / ((M + 1).factorial : ℝ)) := by gcongr
    _ ≤ 4 * (5502 / 10000) * ((pmax : ℝ) / 2 ^ P) *
        ((2 * π * (5502 / 10000) * ((eta : ℝ) / 2 ^ P)) ^ (M + 1) / ((M + 1).factorial : ℝ)) := by
        have : 0 ≤ (5502 / 10000 : ℝ) * ((pmax : ℝ) / 2 ^ P) *
            ((2 * π * (5502 / 10000) * ((eta : ℝ) / 2 ^ P)) ^ (M + 1) / ((M + 1).factorial : ℝ)) := by positivity
        linarith
    _ = _ := by ring

/-! ## One piece in `y` -/

theorem lowPieceOK_sound {n k M N dm : ℕ} {gs : List GGroup} {pgs : List PG4} {sps : List GSpec}
    {cos : List (ℕ × ℕ × ℤ × ℕ)} {ps : List PPiece} {pmax R base : ℕ} {lo : ℤ} {w : ℕ}
    (hgs : List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs)
    (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2)
    (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1) (hpm : pmaxHi ps ≤ pmax)
    (h : lowPieceOK P n k M N dm pgs sps cos ps (ps.map (pieceMoms P M N)) pmax R base lo w = true) :
    ∀ y, (lo : ℝ) / 2 ^ P ≤ y → y ≤ ((lo + (w : ℤ) : ℤ) : ℝ) / 2 ^ P →
      ((R + base : ℕ) : ℝ) / 2 ^ P < 1 - tauSum (vTerms gs sps cos) 0 y + PhatS P ps y := by
  intro y hy1 hy2
  have hbnd := chain_bounds 0 ps hch hord
  unfold lowPieceOK at h
  dsimp only at h
  set η := w - w / 2 with hη
  set y0 : ℤ := lo + ((w / 2 : ℕ) : ℤ) with hy0
  rcases hA : vJet P M (expB' P n) (cosSinTurn P n k) pgs sps cos ⟨y0, 0⟩ with _ | V
  · simp [hA] at h
  rcases hB : vJet P (M + 1) (expH P n) (cosSinTurnC P n k) pgs sps cos ⟨y0, η⟩ with _ | V'
  · simp [hA, hB] at h
  rcases hC : phatJet P n k M N ps (ps.map (pieceMoms P M N)) (ps.map pmaxOne) ⟨y0, 0⟩ with _ | H
  · simp [hA, hB, hC] at h
  simp only [hA, hB, hC, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hpoly⟩ := h
  set L := vTerms gs sps cos with hL
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  set c : ℝ := (y0 : ℝ) / 2 ^ P with hc
  set er : ℝ := (η : ℝ) / 2 ^ P with her
  have her0 : 0 ≤ er := by positivity
  -- jets at the centre
  have hV := memL_vJet (fun hx hX => mem_expB' hx hX) (fun hu hU => mem_cosSinTurn hu hU) (mem_point P y0) hgs hcos hA
  have hH := memL_phatJet hord (fun pc hpc => (hbnd pc hpc).2) hC
  -- the remainder coefficient of v on the piece
  set Mv := (V'.getD (M + 1) ⟨0, 0⟩).absHi with hMvdef
  have hM : ∀ x ∈ Set.Icc (c - er) (c + er), |tauSum L (M + 1) x| ≤ (Mv : ℝ) / 2 ^ P := by
    intro x hx
    have hxY : mem P x (⟨y0, η⟩ : Ball) := mem_center (by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
    have hJ' := memL_vJet (fun hx hX => mem_expH hx hX) (fun hu hU => mem_cosSinTurnC hu hU) hxY hgs hcos hB
    have := memL_getD hJ' (i := M + 1) (by omega)
    rw [hMvdef]
    exact abs_le_absHi this
  -- the piece lies in [c - er, c + er]
  have hw2 : (w / 2 : ℕ) + η = w := by rw [hη]; omega
  have hw1 : η ≥ (w / 2 : ℕ) := by rw [hη]; omega
  have hcl : c - er ≤ (lo : ℝ) / 2 ^ P := by
    rw [hc, her, ← sub_div, div_le_div_iff_of_pos_right hP, hy0, Int.cast_add, Int.cast_natCast]
    have : ((w / 2 : ℕ) : ℝ) ≤ (η : ℝ) := by exact_mod_cast hw1
    linarith
  have hcr : ((lo + (w : ℤ) : ℤ) : ℝ) / 2 ^ P ≤ c + er := by
    rw [hc, her, ← add_div, div_le_div_iff_of_pos_right hP, hy0, Int.cast_add, Int.cast_add, Int.cast_natCast,
      Int.cast_natCast]
    have : ((w / 2 : ℕ) : ℝ) + (η : ℝ) = (w : ℝ) := by exact_mod_cast hw2
    linarith
  have hy : y ∈ Set.Icc (c - er) (c + er) := ⟨by linarith, by linarith⟩
  have hyc : |y - c| ≤ er := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  -- Taylor of the included v terms
  have hTay := taylorK (m := M) (T := fun j => tauSum L j) (fun j _ x => hasDerivAt_tauSum L j x) hM y hy
  -- Taylor of P̂
  have hPh := phat_taylor (P := P) hch hord c (y - c) M
  rw [show c + (y - c) = y by ring] at hPh
  have hPhR := phatRem_bound (P := P) (M := M) hpm (hyc.trans (le_of_eq her))
  -- the coefficients T
  have h1 : MemL P ((List.range (M + 1)).map fun j => if j = 0 then (1 : ℝ) else 0) (ofInt P 1 :: zeroL M) := by
    rw [List.range_succ_eq_map, List.map_cons]
    refine List.Forall₂.cons (by simpa using mem_ofInt P 1) ?_
    have := memL_zeroL (P := P) M
    simpa [List.map_map, Function.comp_def] using this
  have hT := memL_addL (memL_subL h1 hV) hH
  rw [zipWith_sub_range, zipWith_add_range] at hT
  unfold addL at hT
  set Tj : ℕ → ℝ := fun j => (if j = 0 then (1 : ℝ) else 0) - tauSum L j c + HJ P ps j c with hTj
  -- scaled coefficients
  have hscale := memL_scaleRat (P := P) (w := η) (d := 2 ^ P) (by positivity) hT
  set bs := scaleRat η (2 ^ P) (List.zipWith add (List.zipWith sub (ofInt P 1 :: zeroL M) V) H) with hbs
  -- the normalized variable
  set σ : ℝ := if er = 0 then 0 else (y - c) / er with hσdef
  have hσ1 : |σ| ≤ 1 := by
    rw [hσdef]; split_ifs with he
    · simp
    · rw [abs_div, abs_of_nonneg her0]
      exact div_le_one_of_le₀ hyc her0
  have hyσ : y - c = er * σ := by
    rw [hσdef]; split_ifs with he
    · rw [he] at hyc; have := abs_nonpos_iff.mp hyc; rw [this]; ring
    · field_simp
  have hclose := horn_close hσ1 hscale
  have hblen : (bs.map (·.m)).length = M + 1 := by
    have := hscale.length_eq
    simp only [List.length_map, List.length_range] at this
    rw [List.length_map]; omega
  have hK := polyOK_top hblen hpoly hσ1
  -- the Taylor sum of 1 - v + P̂ in σ
  have hsum : hornR ((List.range (M + 1)).map fun j =>
      ((if j = 0 then (1 : ℝ) else 0) - tauSum L j c + HJ P ps j c) * (((η : ℕ) : ℝ) / ((2 ^ P : ℕ) : ℝ)) ^ j) σ =
      1 - npoly (fun j => tauSum L j) c M y + ∑ j ∈ range (M + 1), HJ P ps j c * (y - c) ^ j := by
    rw [hornR_range, npoly]
    have e : ∀ j, ((if j = 0 then (1 : ℝ) else 0) - tauSum L j c + HJ P ps j c) *
        (((η : ℕ) : ℝ) / ((2 ^ P : ℕ) : ℝ)) ^ j * σ ^ j =
        (if j = 0 then (1 : ℝ) else 0) * (y - c) ^ j - tauSum L j c * (y - c) ^ j + HJ P ps j c * (y - c) ^ j := by
      intro j
      rw [hyσ, her]; push_cast; rw [mul_pow]; ring
    rw [sum_congr rfl (fun j _ => e j), sum_add_distrib, sum_sub_distrib]
    have e1 : ∑ j ∈ range (M + 1), (if j = 0 then (1 : ℝ) else 0) * (y - c) ^ j = 1 := by
      rw [sum_range_succ']; simp
    rw [e1]
  rw [hsum] at hclose
  -- the remainder of v
  have hrem : (Mv : ℝ) / 2 ^ P * |y - c| ^ (M + 1) ≤
      ((cdiv (Mv * η ^ (M + 1)) (2 ^ (P * (M + 1))) : ℕ) : ℝ) / 2 ^ P := by
    have h1 : |y - c| ^ (M + 1) ≤ er ^ (M + 1) := pow_le_pow_left₀ (abs_nonneg _) hyc (M + 1)
    have h2 := cdiv_spec (Mv * η ^ (M + 1)) (2 ^ (P * (M + 1))) (by positivity)
    have h3 : (Mv : ℝ) / 2 ^ P * er ^ (M + 1) =
        ((Mv * η ^ (M + 1) : ℕ) : ℝ) / ((2 ^ (P * (M + 1)) : ℕ) : ℝ) / 2 ^ P := by
      rw [her]; push_cast; rw [pow_mul, div_pow]; field_simp
    calc (Mv : ℝ) / 2 ^ P * |y - c| ^ (M + 1) ≤ (Mv : ℝ) / 2 ^ P * er ^ (M + 1) := by gcongr
      _ = ((Mv * η ^ (M + 1) : ℕ) : ℝ) / ((2 ^ (P * (M + 1)) : ℕ) : ℝ) / 2 ^ P := h3
      _ ≤ ((cdiv (Mv * η ^ (M + 1)) (2 ^ (P * (M + 1))) : ℕ) : ℝ) / 2 ^ P := by gcongr
  have hT1 := (abs_le.mp hTay).2
  have hc2 := (abs_le.mp hclose).1
  have hP2 := (abs_le.mp hPh).1
  have hKr := div_lt_div_of_pos_right hK hP
  simp only [Nat.cast_add, add_div] at hKr ⊢
  linarith

/-! ## Runs and segments -/

theorem lrunOK_sound {n k M N dm : ℕ} {gs : List GGroup} {pgs : List PG4} {sps : List GSpec}
    {cos : List (ℕ × ℕ × ℤ × ℕ)} {ps : List PPiece} {pmax R base w : ℕ}
    (hgs : List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs)
    (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2)
    (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1) (hpm : pmaxHi ps ≤ pmax) :
    ∀ (cnt : ℕ) (lo : ℤ), 0 < cnt →
      lrunOK P n k M N dm pgs sps cos ps (ps.map (pieceMoms P M N)) pmax R base w cnt lo = true →
      ∀ y, (lo : ℝ) / 2 ^ P ≤ y → y ≤ ((lo + ((w * cnt : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P →
        ((R + base : ℕ) : ℝ) / 2 ^ P < 1 - tauSum (vTerms gs sps cos) 0 y + PhatS P ps y := by
  intro cnt
  induction cnt with
  | zero => intro lo h; omega
  | succ c ih =>
    intro lo _ h y hy1 hy2
    simp only [lrunOK, Bool.and_eq_true] at h
    obtain ⟨hp, hr⟩ := h
    rcases le_or_gt y (((lo + (w : ℤ) : ℤ) : ℝ) / 2 ^ P) with hle | hgt
    · exact lowPieceOK_sound hgs hcos hch hord hpm hp y hy1 hle
    · rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · subst hc0
        simp only [zero_add, mul_one] at hy2
        exact absurd hy2 (not_le.mpr hgt)
      · refine ih (lo + (w : ℤ)) hc0 hr y hgt.le ?_
        convert hy2 using 3
        push_cast; ring

theorem lrunsOK_sound {n k M N dm : ℕ} {gs : List GGroup} {pgs : List PG4} {sps : List GSpec}
    {cos : List (ℕ × ℕ × ℤ × ℕ)} {ps : List PPiece} {pmax R base : ℕ}
    (hgs : List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs)
    (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2)
    (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1) (hpm : pmaxHi ps ≤ pmax) :
    ∀ (ws : List (ℕ × ℕ)) (lo : ℤ), ws ≠ [] → (∀ r ∈ ws, 0 < r.2) →
      lrunsOK P n k M N dm pgs sps cos ps (ps.map (pieceMoms P M N)) pmax R base lo ws = true →
      ∀ y, (lo : ℝ) / 2 ^ P ≤ y → y ≤ (runsEnd lo ws : ℝ) / 2 ^ P →
        ((R + base : ℕ) : ℝ) / 2 ^ P < 1 - tauSum (vTerms gs sps cos) 0 y + PhatS P ps y := by
  intro ws
  induction ws with
  | nil => intro _ h; exact absurd rfl h
  | cons r rs ih =>
    intro lo _ hpos h y hy1 hy2
    obtain ⟨w, cnt⟩ := r
    simp only [lrunsOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hc : 0 < cnt := hpos (w, cnt) (by simp)
    rcases le_or_gt y (((lo + ((w * cnt : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P) with hle | hgt
    · exact lrunOK_sound hgs hcos hch hord hpm cnt lo hc h1 y hy1 hle
    · cases rs with
      | nil =>
        simp only [runsEnd, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hy2
        exact absurd hy2 (not_le.mpr hgt)
      | cons r' rs' =>
        refine ih _ (by simp) (fun r hr => hpos r (by simp [hr])) h2 y hgt.le ?_
        convert hy2 using 2
        simp only [runsEnd, List.map_cons, List.sum_cons]
        push_cast; ring

/-- A segment: `1 - v + P̂ > m + 2rε` on `[s.lo, runsEnd]` (all Gaussian terms, units `2^-P`). -/
theorem lsegOK_sound (c : LCfg) (gs : List GGroup) (cos : List (ℕ × ℕ × ℤ × ℕ)) (ps : List PPiece) (s : LSeg)
    (h : lsegOK c gs cos ps s = true) (hne : s.ws ≠ []) (hpos : ∀ r ∈ s.ws, 0 < r.2)
    (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2) (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1) :
    ∀ y, (s.lo : ℝ) / 2 ^ c.P ≤ y → y ≤ (runsEnd s.lo s.ws : ℝ) / 2 ^ c.P →
      ((c.m + (mul c.P (mulInt 2 (ofRat c.P 2751 5000)) ⟨(c.eps : ℤ), 0⟩).absHi : ℕ) : ℝ) / 2 ^ c.P <
        1 - (vsum (gs.flatMap GGroup.triples) y + tauSum (cosTerms cos) 0 y) + PhatS c.P ps y := by
  intro y hy1 hy2
  unfold lsegOK at h
  split at h
  · rename_i pgs hpgs
    split at h
    · rename_i R hR
      have hF := prepGroupsV_ok hpgs
      have hom := omitAllV_sound hy1 hy2 hF hR
      have hrun := lrunsOK_sound hF hcos hch hord le_rfl s.ws s.lo hne hpos h y hy1 hy2
      have hsplit : tauSum (vTerms gs s.sps cos) 0 y = tauSum (inclAllV gs s.sps) 0 y + tauSum (cosTerms cos) 0 y := by
        rw [vTerms, tauSum_append]
      rw [hsplit] at hrun
      have := (abs_le.mp hom).2
      push_cast at hrun ⊢
      rw [add_div] at hrun
      linarith
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end SignUnc.Chk
