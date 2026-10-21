import SignUnc.LowSound3
import SignUnc.LowTaylor

/-!
# Soundness of the lower checker, part 4: moments of `P` and `|ρ| ≤ δ` (`rhoOK`)

Pieces in the normalized variable `σ ∈ [-1, 1]` (`t = c + ησ`), polynomial integrals (`intPow`, `mulLin`, `momLin`,
`pieceMoms`, `momAll`), and `rhoOK_sound`: `|P̂(x) - ψ(x)| + 2rε ≤ δ` for `|x| ≤ r` (the cosine Taylor expansion
with the explicit remainder of `taylor_cos`).
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Finset MeasureTheory intervalIntegral

variable {P : ℕ}

/-! ## Pieces in the normalized variable -/

/-- The centre of a piece in `ℝ`. -/
noncomputable def pcR (pc : PPiece) : ℝ := ((pc.1 + pc.2.1 : ℕ) : ℝ) / 20000
/-- The half-width of a piece in `ℝ`. -/
noncomputable def peR (pc : PPiece) : ℝ := ((pc.2.1 - pc.1 : ℕ) : ℝ) / 20000
/-- The piece polynomial in `σ`: `p(σ) = Σ_i (B_i/2^P) σ^i`. -/
noncomputable def pR (P : ℕ) (pc : PPiece) (σ : ℝ) : ℝ := peval pc.2.2 σ / 2 ^ P

theorem peR_pos {pc : PPiece} (h : pc.1 < pc.2.1) : 0 < peR pc := by
  unfold peR
  have : 0 < pc.2.1 - pc.1 := by omega
  positivity

theorem peR_nonneg (pc : PPiece) : 0 ≤ peR pc := by unfold peR; positivity

theorem continuous_peval : ∀ cs : List ℤ, Continuous (peval cs)
  | [] => by
    show Continuous fun _ => (0 : ℝ)
    exact continuous_const
  | c :: cs => by
    have := continuous_peval cs
    show Continuous fun x => (c : ℝ) + x * peval cs x
    fun_prop

theorem continuous_pR (pc : PPiece) : Continuous (pR P pc) := by
  have := continuous_peval pc.2.2
  unfold pR; fun_prop

theorem peval_eq_sum : ∀ (cs : List ℤ) (x : ℝ), peval cs x = ∑ i ∈ range cs.length, ((cs.getD i 0 : ℤ) : ℝ) * x ^ i
  | [], x => by simp
  | c :: cs, x => by
    rw [peval_cons, peval_eq_sum cs x, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]; congr 1
    refine sum_congr rfl (fun i _ => ?_); ring

theorem Peval_affine {pc : PPiece} (h : pc.1 < pc.2.1) (σ : ℝ) : Peval P pc (peR pc * σ + pcR pc) = pR P pc σ := by
  have he := (peR_pos h).ne'
  unfold Peval pR
  rw [peval_eq_sum, sum_div]
  refine sum_congr rfl (fun i _ => ?_)
  have : (peR pc * σ + pcR pc - ((pc.1 + pc.2.1 : ℕ) : ℝ) / 20000) / (((pc.2.1 - pc.1 : ℕ) : ℝ) / 20000) = σ := by
    rw [show ((pc.1 + pc.2.1 : ℕ) : ℝ) / 20000 = pcR pc from rfl,
      show (((pc.2.1 - pc.1 : ℕ) : ℝ) / 20000) = peR pc from rfl, add_sub_cancel_right, mul_div_cancel_left₀ σ he]
  rw [this]; ring

theorem plo_eq {pc : PPiece} (h : pc.1 ≤ pc.2.1) : plo pc = peR pc * (-1) + pcR pc := by
  unfold plo peR pcR; rw [Nat.cast_sub h]; push_cast; ring

theorem phi_eq {pc : PPiece} (h : pc.1 ≤ pc.2.1) : phi' pc = peR pc * 1 + pcR pc := by
  unfold phi' peR pcR; rw [Nat.cast_sub h]; push_cast; ring

/-- `∫_{lo}^{hi} P_k g = η ∫_{-1}^{1} p(σ) g(ησ + c) dσ`. -/
theorem integral_piece {pc : PPiece} (h : pc.1 < pc.2.1) (g : ℝ → ℝ) :
    ∫ t in plo pc..phi' pc, Peval P pc t * g t =
      peR pc * ∫ σ in (-1 : ℝ)..1, pR P pc σ * g (peR pc * σ + pcR pc) := by
  have he := (peR_pos h).ne'
  have := intervalIntegral.integral_comp_mul_add (a := (-1 : ℝ)) (b := 1) (fun t => Peval P pc t * g t) he (pcR pc)
  simp only [Peval_affine h] at this
  rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ he, one_mul, ← plo_eq h.le, ← phi_eq h.le]

/-- On a piece inside `[0, 5502/10000]`: `0 ≤ c + ησ ≤ 5502/10000` for `|σ| ≤ 1`. -/
theorem piece_t_bounds {pc : PPiece} (hle : pc.1 ≤ pc.2.1) (hhi : pc.2.1 ≤ 5502) {σ : ℝ} (hσ : |σ| ≤ 1) :
    0 ≤ pcR pc + peR pc * σ ∧ pcR pc + peR pc * σ ≤ 5502 / 10000 := by
  have he := peR_nonneg pc
  have h1 := abs_le.mp hσ
  have hlo : pcR pc - peR pc = (pc.1 : ℝ) / 10000 := by unfold pcR peR; rw [Nat.cast_sub hle]; push_cast; ring
  have hhi' : pcR pc + peR pc = (pc.2.1 : ℝ) / 10000 := by unfold pcR peR; rw [Nat.cast_sub hle]; push_cast; ring
  have h5 : ((pc.2.1 : ℕ) : ℝ) ≤ 5502 := by exact_mod_cast hhi
  have h0 : (0 : ℝ) ≤ (pc.1 : ℝ) / 10000 := by positivity
  have hm1 := mul_le_mul_of_nonneg_left h1.1 he
  have hm2 := mul_le_mul_of_nonneg_left h1.2 he
  constructor <;> nlinarith

theorem abs_pR_le (pc : PPiece) {σ : ℝ} (hσ : |σ| ≤ 1) : |pR P pc σ| ≤ (pmaxOne pc : ℝ) / 2 ^ P := by
  unfold pR pmaxOne
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ P)]
  exact div_le_div_of_nonneg_right (abs_peval_le _ hσ) (by positivity)

theorem pmaxOne_le_pmaxHi : ∀ (ps : List PPiece), ∀ pc ∈ ps, pmaxOne pc ≤ pmaxHi ps
  | [], _, h => by simp at h
  | q :: L, pc, h => by
    have e : pmaxHi (q :: L) = max (pmaxOne q) (pmaxHi L) := rfl
    rw [e]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (pmaxOne_le_pmaxHi L pc h) (le_max_right _ _)

theorem chain_end : ∀ (a : ℕ) (ps : List PPiece), chainOK a ps = true → (∀ pc ∈ ps, pc.1 < pc.2.1) → a ≤ 5502
  | a, [], h, _ => by simp only [chainOK, decide_eq_true_eq] at h; omega
  | a, pc :: L, h, hord => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have := chain_end pc.2.1 L h.2 (fun q hq => hord q (by simp [hq]))
    have := hord pc (by simp)
    omega

theorem chain_bounds : ∀ (a : ℕ) (ps : List PPiece), chainOK a ps = true → (∀ pc ∈ ps, pc.1 < pc.2.1) →
    ∀ pc ∈ ps, a ≤ pc.1 ∧ pc.2.1 ≤ 5502
  | a, [], _, _ => by simp
  | a, pc :: L, h, hord => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hL : ∀ q ∈ L, q.1 < q.2.1 := fun q hq => hord q (by simp [hq])
    have ih := chain_bounds pc.2.1 L h2 hL
    have hpc := hord pc (by simp)
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨h1.ge, chain_end _ L h2 hL⟩
    · have := ih q hq; omega

theorem chain_width_sum : ∀ (a : ℕ) (ps : List PPiece), chainOK a ps = true → (∀ pc ∈ ps, pc.1 < pc.2.1) →
    (ps.map fun pc => 2 * peR pc).sum = (5502 - (a : ℝ)) / 10000
  | a, [], h, _ => by simp only [chainOK, decide_eq_true_eq] at h; subst h; simp
  | a, pc :: L, h, hord => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.map_cons, List.sum_cons, chain_width_sum pc.2.1 L h2 (fun q hq => hord q (by simp [hq]))]
    unfold peR; rw [Nat.cast_sub (hord pc (by simp)).le, h1]; ring

/-! ## Real coefficient lists -/

theorem continuous_hornR : ∀ qs : List ℝ, Continuous (hornR qs)
  | [] => by
    show Continuous fun _ => (0 : ℝ)
    exact continuous_const
  | q :: qs => by
    have := continuous_hornR qs
    show Continuous fun σ => q + σ * hornR qs σ
    fun_prop

theorem hornR_zipWith_add : ∀ (a b : List ℝ), a.length = b.length → ∀ x,
    hornR (List.zipWith (· + ·) a b) x = hornR a x + hornR b x
  | [], [], _, x => by simp [hornR]
  | a :: as, b :: bs, h, x => by
    simp only [List.zipWith_cons_cons, hornR]
    rw [hornR_zipWith_add as bs (by simpa using h) x]; ring
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem hornR_map_mul (s : ℝ) : ∀ (a : List ℝ) (x : ℝ), hornR (a.map (s * ·)) x = s * hornR a x
  | [], x => by simp [hornR]
  | a :: as, x => by
    simp only [List.map_cons, hornR]
    rw [hornR_map_mul s as x]; ring

theorem hornR_append_zero : ∀ (a : List ℝ) (x : ℝ), hornR (a ++ [0]) x = hornR a x
  | [], x => by simp [hornR]
  | a :: as, x => by simp only [List.cons_append, hornR]; rw [hornR_append_zero as x]

theorem hornR_map_div (cs : List ℤ) (x : ℝ) : hornR (cs.map fun B : ℤ => (B : ℝ) / 2 ^ P) x = peval cs x / 2 ^ P := by
  induction cs with
  | nil => simp [hornR]
  | cons c cs ih => simp only [List.map_cons, hornR, peval_cons, ih]; ring

/-- The coefficients of `q(σ) (c + eσ)`. -/
noncomputable def mulLinR (c e : ℝ) (q : List ℝ) : List ℝ :=
  List.zipWith (· + ·) (q.map (c * ·) ++ [0]) (0 :: q.map (e * ·))

theorem hornR_mulLinR (c e : ℝ) (q : List ℝ) (x : ℝ) : hornR (mulLinR c e q) x = hornR q x * (c + e * x) := by
  unfold mulLinR
  rw [hornR_zipWith_add _ _ (by simp), hornR_append_zero, hornR_map_mul]
  simp only [hornR]
  rw [hornR_map_mul]; ring

theorem memL_map_fun {xs : List ℝ} {bs : List Ball} (h : MemL P xs bs) {f : ℝ → ℝ} {F : Ball → Ball}
    (hF : ∀ x b, mem P x b → mem P (f x) (F b)) : MemL P (xs.map f) (bs.map F) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih => exact List.Forall₂.cons (hF _ _ hx) ih

theorem memL_map_same {f : ℕ → ℝ} {g : ℕ → Ball} (h : ∀ n, mem P (f n) (g n)) (l : List ℕ) :
    MemL P (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons (h a) ih

theorem memL_mulLin {c e : ℝ} {C E : Ball} (hc : mem P c C) (he : mem P e E) {q : List ℝ} {Q : List Ball}
    (h : MemL P q Q) : MemL P (mulLinR c e q) (mulLin P C E Q) := by
  have h1 : MemL P (q.map (c * ·) ++ [0]) (Q.map (mul P C) ++ [⟨0, 0⟩]) :=
    List.rel_append (memL_map_mul hc h) (List.Forall₂.cons mem_zero_ball List.Forall₂.nil)
  have h2 : MemL P (0 :: q.map (e * ·)) (⟨0, 0⟩ :: Q.map (mul P E)) :=
    List.Forall₂.cons mem_zero_ball (memL_map_mul he h)
  have := memL_addL h1 h2
  unfold addL at this
  exact this

/-! ## Polynomial integrals over `[-1, 1]` -/

theorem integral_pow_sym (m : ℕ) : ∫ σ in (-1 : ℝ)..1, σ ^ m = if m % 2 = 0 then 2 / ((m : ℝ) + 1) else 0 := by
  rw [integral_pow]
  split_ifs with h
  · have : Odd (m + 1) := by rw [Nat.odd_iff]; omega
    rw [this.neg_one_pow, one_pow]; ring
  · have : Even (m + 1) := by rw [Nat.even_iff]; omega
    rw [this.neg_one_pow, one_pow]; ring

theorem mem_intPowAux (n : ℕ) : ∀ (e : ℕ) {qs : List ℝ} {Q : List Ball}, MemL P qs Q →
    mem P (∫ σ in (-1 : ℝ)..1, hornR qs σ * σ ^ (e + n)) (intPowAux n e Q)
  | e, [], [], List.Forall₂.nil => by
    simp only [hornR, zero_mul, intervalIntegral.integral_zero, intPowAux]; exact mem_zero_ball
  | e, q :: qs, b :: bs, List.Forall₂.cons hq h => by
    have ih := mem_intPowAux n (e + 1) h
    have hc := continuous_hornR qs
    have hsplit : ∫ σ in (-1 : ℝ)..1, hornR (q :: qs) σ * σ ^ (e + n) =
        q * (∫ σ in (-1 : ℝ)..1, σ ^ (e + n)) + ∫ σ in (-1 : ℝ)..1, hornR qs σ * σ ^ (e + 1 + n) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        ((by fun_prop : Continuous fun σ : ℝ => q * σ ^ (e + n)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun σ : ℝ => hornR qs σ * σ ^ (e + 1 + n)).intervalIntegrable _ _)]
      congr 1; funext σ; simp only [hornR]; ring
    rw [hsplit, integral_pow_sym]
    simp only [intPowAux]
    split_ifs with h2
    · have hd := mem_divNat (P := P) (d := e + n + 1) (by omega) (mem_mulInt 2 hq)
      have e3 : q * (2 / (((e + n : ℕ) : ℝ) + 1)) = ((2 : ℤ) : ℝ) * q / ((e + n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [e3]; exact mem_add hd ih
    · rw [mul_zero, zero_add]; exact ih

theorem mem_intPow (n : ℕ) {qs : List ℝ} {Q : List Ball} (h : MemL P qs Q) :
    mem P (∫ σ in (-1 : ℝ)..1, hornR qs σ * σ ^ n) (intPow Q n) := by
  have := mem_intPowAux n 0 h
  simpa [intPow] using this

theorem memL_momLin {c e : ℝ} {C E : Ball} (hc : mem P c C) (he : mem P e E) :
    ∀ (N : ℕ) {q : List ℝ} {Q : List Ball}, MemL P q Q →
      MemL P ((List.range N).map fun j => ∫ σ in (-1 : ℝ)..1, hornR q σ * (c + e * σ) ^ j) (momLin P C E N Q)
  | 0, q, Q, _ => by simp [momLin]
  | N + 1, q, Q, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [momLin]
    refine List.Forall₂.cons ?_ ?_
    · have := mem_intPow 0 h
      simpa using this
    · have := memL_momLin hc he N (memL_mulLin hc he h)
      convert this using 2
      funext j
      simp only [Function.comp_apply, hornR_mulLinR, pow_succ]
      congr 1; funext σ; ring

theorem forall₂_pieceMomsAux {c e : ℝ} {C E : Ball} (hc : mem P c C) (he : mem P e E) (N : ℕ) :
    ∀ (M : ℕ) {q : List ℝ} {Q : List Ball}, MemL P q Q →
      List.Forall₂ (fun (j : ℕ) (row : List Ball) =>
        MemL P ((List.range N).map fun n => ∫ σ in (-1 : ℝ)..1, hornR q σ * (c + e * σ) ^ j * σ ^ n) row)
        (List.range M) (pieceMomsAux P N C E M Q)
  | 0, q, Q, _ => by simp [pieceMomsAux]
  | M + 1, q, Q, h => by
    rw [List.range_succ_eq_map]
    simp only [pieceMomsAux]
    refine List.Forall₂.cons ?_ ?_
    · refine memL_map_same (fun n => ?_) _
      have := mem_intPow n h
      simpa using this
    · have := forall₂_pieceMomsAux hc he N M (memL_mulLin hc he h)
      rw [List.forall₂_map_left_iff]
      refine this.imp (fun j row hrow => ?_)
      convert hrow using 2
      funext n
      congr 1; funext σ; rw [hornR_mulLinR, Nat.succ_eq_add_one]; ring

theorem mem_pcen (pc : PPiece) : mem P (pcR pc) (pcen P pc) := by
  have := mem_ofRat P ((pc.1 + pc.2.1 : ℕ) : ℤ) 20000 (by norm_num)
  unfold pcen pcR
  convert this using 1

theorem mem_peta (pc : PPiece) : mem P (peR pc) (peta P pc) := by
  have := mem_ofRat P ((pc.2.1 - pc.1 : ℕ) : ℤ) 20000 (by norm_num)
  unfold peta peR
  convert this using 1

theorem memL_pcoef (pc : PPiece) : MemL P (pc.2.2.map fun B : ℤ => (B : ℝ) / 2 ^ P) (pcoef pc) := by
  unfold pcoef
  induction pc.2.2 with
  | nil => exact List.Forall₂.nil
  | cons B L ih => exact List.Forall₂.cons (mem_point P B) ih

theorem forall₂_pieceMoms (M N : ℕ) (pc : PPiece) :
    List.Forall₂ (fun (j : ℕ) (row : List Ball) =>
        MemL P ((List.range N).map fun n => ∫ σ in (-1 : ℝ)..1, pR P pc σ * (pcR pc + peR pc * σ) ^ j * σ ^ n) row)
      (List.range (M + 1)) (pieceMoms P M N pc) := by
  have := forall₂_pieceMomsAux (mem_pcen pc) (mem_peta pc) N (M + 1) (memL_pcoef (P := P) pc)
  unfold pieceMoms
  refine this.imp (fun j row hrow => ?_)
  convert hrow using 2
  funext n
  congr 1; funext σ; rw [hornR_map_div]; rfl

/-- `μ_j = Σ_k 2 η_k ∫_{-1}^{1} p_k(σ) (c_k + η_k σ)^j dσ`. -/
noncomputable def muR (P : ℕ) (ps : List PPiece) (j : ℕ) : ℝ :=
  (ps.map fun pc => 2 * (peR pc * ∫ σ in (-1 : ℝ)..1, pR P pc σ * (pcR pc + peR pc * σ) ^ j)).sum

theorem memL_momAll (J : ℕ) : ∀ ps : List PPiece, MemL P ((List.range J).map (muR P ps)) (momAll P J ps)
  | [] => by
    simp only [momAll]
    have := memL_zeroL (P := P) J
    convert this using 2
    funext j; simp [muR]
  | pc :: L => by
    simp only [momAll]
    have h1 := memL_momLin (mem_pcen pc) (mem_peta pc) J (memL_pcoef (P := P) pc)
    have h2 := memL_map_fun h1 (f := fun m => 2 * (peR pc * m))
      (F := fun m => mulInt 2 (mul P (peta P pc) m)) (fun x b hx => by
        have := mem_mulInt 2 (mem_mul (mem_peta (P := P) pc) hx)
        simpa using this)
    rw [List.map_map] at h2
    have := memL_addL h2 (memL_momAll J L)
    rw [zipWith_add_range] at this
    convert this using 2
    funext j
    simp only [muR, List.map_cons, List.sum_cons, Function.comp_apply, hornR_map_div]
    rfl

/-! ## `|ρ| ≤ δ` -/

/-- `(-1)^n (2π)^(2n) / (2n)!`. -/
noncomputable def fcos (n : ℕ) : ℝ := (-1) ^ n * (2 * π) ^ (2 * n) / ((2 * n).factorial : ℝ)

theorem fcos_succ (n : ℕ) :
    -(fcos n * (2 * π * (2 * π))) / (((2 * n + 1) * (2 * n + 2) : ℕ) : ℝ) = fcos (n + 1) := by
  unfold fcos
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  have h0 : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  field_simp
  ring

/-- The `n`-th coefficient of `ψ` (zero beyond the list). -/
noncomputable def qR (psi : List (ℤ × ℕ)) (n : ℕ) : ℝ := ((psi.getD n (0, 1)).1 : ℝ) / (psi.getD n (0, 1)).2

theorem Tpoly_psiR : ∀ (psi : List (ℤ × ℕ)) (N : ℕ), psi.length ≤ N → ∀ x : ℝ,
    Tpoly (psiR psi) 0 x = ∑ n ∈ range N, qR psi n * x ^ (2 * n)
  | [], N, _, x => by simp [psiR, Tpoly, qR]
  | q :: L, N, h, x => by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at h; omega⟩
    rw [sum_range_succ', psiR, Tpoly, Tpoly, Tpoly_psiR L N' (by simp at h; omega) x]
    simp only [qR, List.getD_cons_succ, List.getD_cons_zero, zero_add, mul_zero, pow_zero, mul_one]
    rw [← mul_assoc, mul_sum, add_comm]
    congr 1
    refine sum_congr rfl (fun n _ => ?_)
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]; ring

theorem memL_rhoCoefAux {tp2 : Ball} (htp2 : mem P (2 * π * (2 * π)) tp2) (μ : ℕ → ℝ) (qf : ℕ → ℝ) :
    ∀ (K n : ℕ) {fac : Ball} {ms : List Ball} {qs : List Ball},
      mem P (fcos n) fac →
      MemL P ((List.range (2 * K)).map fun i => μ (2 * n + i)) ms →
      (∀ i, mem P (qf (n + i)) (qs.getD i ⟨0, 0⟩)) →
      MemL P ((List.range K).map fun i => fcos (n + i) * μ (2 * (n + i)) - qf (n + i))
        (rhoCoefAux P tp2 n fac ms qs)
  | 0, n, fac, ms, qs, _, hms, _ => by
    simp only [mul_zero, List.range_zero, List.map_nil] at hms
    cases hms
    simp [rhoCoefAux]
  | K + 1, n, fac, ms, qs, hfac, hms, hqs => by
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring] at hms
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map] at hms
    cases hms with
    | cons hm0 hms1 =>
      cases hms1 with
      | cons hm1 hrest =>
        rename_i m0 m1 rest
        rw [List.range_succ_eq_map, List.map_cons]
        simp only [rhoCoefAux]
        refine List.Forall₂.cons ?_ ?_
        · have hq0 := hqs 0
          have e0 : qs.headD ⟨0, 0⟩ = qs.getD 0 ⟨0, 0⟩ := by cases qs <;> rfl
          rw [e0]
          simp only [add_zero] at hq0 hm0 ⊢
          exact mem_sub (mem_mul hfac hm0) hq0
        · have hfac' : mem P (fcos (n + 1))
              (divNat ((2 * n + 1) * (2 * n + 2)) (neg (mul P fac tp2))) := by
            rw [← fcos_succ]
            exact mem_divNat (by positivity) (mem_neg (mem_mul hfac htp2))
          have hrest' : MemL P ((List.range (2 * K)).map fun i => μ (2 * (n + 1) + i)) rest := by
            convert hrest using 2
            funext i
            simp only [Function.comp_apply, Nat.succ_eq_add_one]
            congr 1; ring
          have hqs' : ∀ i, mem P (qf (n + 1 + i)) (qs.tail.getD i ⟨0, 0⟩) := by
            intro i
            have := hqs (i + 1)
            rw [show n + (i + 1) = n + 1 + i by ring] at this
            cases qs with
            | nil => simpa using this
            | cons a qs' => simpa using this
          have := memL_rhoCoefAux htp2 μ qf K (n + 1) hfac' hrest' hqs'
          rw [List.map_map]
          convert this using 2
          funext i
          simp only [Function.comp_apply]
          rw [show n + (i + 1) = n + 1 + i by ring]

theorem mem_powB {x : ℝ} {X : Ball} (hx : mem P x X) : ∀ n, mem P (x ^ n) (powB P X n)
  | 0 => by
    show mem P (x ^ 0) (ofInt P 1)
    simpa using mem_ofInt P 1
  | n + 1 => by rw [pow_succ]; exact mem_mul (mem_powB hx n) hx

theorem zipWith_range (f : ℝ → ℝ → ℝ) (g h : ℕ → ℝ) (n : ℕ) :
    List.zipWith f ((List.range n).map g) ((List.range n).map h) = (List.range n).map fun i => f (g i) (h i) := by
  rw [List.zipWith_map]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.zipWith_append (by simp), ih]
    simp

theorem sum_abs_mul_le {xs ys : List ℝ} {bs cs : List Ball} (h1 : MemL P xs bs) (h2 : MemL P ys cs) :
    (List.zipWith (fun x y => |x| * y) xs ys).sum ≤
      (((List.zipWith (fun b p => (mul P (absB b) p).absHi) bs cs).sum : ℕ) : ℝ) / 2 ^ P := by
  induction h1 generalizing ys cs with
  | nil => simp
  | cons hx _ ih =>
    cases h2 with
    | nil => simp
    | cons hy h2' =>
      simp only [List.zipWith_cons_cons, List.sum_cons, Nat.cast_add, add_div]
      have := abs_le_absHi (mem_mul (mem_absB hx) hy)
      exact add_le_add ((le_abs_self _).trans this) (ih h2')

theorem sum_range_listSum {α : Type*} (L : List α) (N : ℕ) (f : ℕ → α → ℝ) :
    ∑ n ∈ range N, (L.map (f n)).sum = (L.map fun a => ∑ n ∈ range N, f n a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, sum_add_distrib, ih]

/-- One piece: `2 ∫ P_k cos(2πx·)` against its cosine expansion of order `N`. -/
theorem piece_cos_err {pc : PPiece} (hlt : pc.1 < pc.2.1) (hhi : pc.2.1 ≤ 5502) {x : ℝ}
    (hx : |x| ≤ 5502 / 10000) (N : ℕ) :
    |2 * (∫ t in plo pc..phi' pc, Peval P pc t * Real.cos (2 * π * x * t)) -
      ∑ n ∈ range N, fcos n * x ^ (2 * n) *
        (2 * (peR pc * ∫ σ in (-1 : ℝ)..1, pR P pc σ * (pcR pc + peR pc * σ) ^ (2 * n)))| ≤
    2 * peR pc * (2 * ((pmaxOne pc : ℝ) / 2 ^ P *
      ((2 * π * (5502 / 10000) * (5502 / 10000)) ^ (2 * N) / ((2 * N).factorial : ℝ)))) := by
  have he := peR_pos hlt
  have hpc := continuous_pR (P := P) pc
  rw [integral_piece hlt]
  set T : ℝ → ℝ := fun σ => pcR pc + peR pc * σ with hT
  set B : ℝ := (2 * π * (5502 / 10000) * (5502 / 10000)) ^ (2 * N) / ((2 * N).factorial : ℝ) with hB
  set g : ℝ → ℝ := fun σ => ∑ n ∈ range N, (-1) ^ n * (2 * π * x * T σ) ^ (2 * n) / ((2 * n).factorial : ℝ)
    with hg
  have hTc : Continuous T := by rw [hT]; fun_prop
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hterm : ∀ n, fcos n * x ^ (2 * n) * (2 * (peR pc * ∫ σ in (-1 : ℝ)..1, pR P pc σ * T σ ^ (2 * n))) =
      2 * (peR pc * ∫ σ in (-1 : ℝ)..1,
        pR P pc σ * ((-1) ^ n * (2 * π * x * T σ) ^ (2 * n) / ((2 * n).factorial : ℝ))) := by
    intro n
    have : (fun σ => pR P pc σ * ((-1) ^ n * (2 * π * x * T σ) ^ (2 * n) / ((2 * n).factorial : ℝ))) =
        fun σ => (fcos n * x ^ (2 * n)) * (pR P pc σ * T σ ^ (2 * n)) := by
      funext σ; unfold fcos; rw [mul_pow, mul_pow]; ring
    rw [this, intervalIntegral.integral_const_mul]; ring
  have hsum : ∑ n ∈ range N, fcos n * x ^ (2 * n) * (2 * (peR pc * ∫ σ in (-1 : ℝ)..1, pR P pc σ * T σ ^ (2 * n))) =
      2 * (peR pc * ∫ σ in (-1 : ℝ)..1, pR P pc σ * g σ) := by
    have hfun : (fun σ => pR P pc σ * g σ) = fun σ => ∑ n ∈ range N,
        pR P pc σ * ((-1) ^ n * (2 * π * x * T σ) ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
      funext σ
      show pR P pc σ * (∑ n ∈ range N, (-1) ^ n * (2 * π * x * T σ) ^ (2 * n) / ((2 * n).factorial : ℝ)) = _
      rw [mul_sum]
    rw [hfun, intervalIntegral.integral_finsetSum (fun n _ => (by fun_prop : Continuous fun σ =>
        pR P pc σ * ((-1) ^ n * (2 * π * x * T σ) ^ (2 * n) / ((2 * n).factorial : ℝ))).intervalIntegrable _ _),
      mul_sum, mul_sum]
    exact sum_congr rfl (fun n _ => hterm n)
  rw [hsum]
  have hcos : ∀ σ, Real.cos (2 * π * x * (peR pc * σ + pcR pc)) = Real.cos (2 * π * x * T σ) := by
    intro σ; rw [hT]; ring_nf
  simp only [hcos]
  rw [← mul_sub, ← mul_sub, ← intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun σ => pR P pc σ * Real.cos (2 * π * x * T σ)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun σ => pR P pc σ * g σ).intervalIntegrable _ _)]
  have hbd : ∀ σ ∈ Set.uIoc (-1 : ℝ) 1, ‖pR P pc σ * Real.cos (2 * π * x * T σ) - pR P pc σ * g σ‖ ≤
      (pmaxOne pc : ℝ) / 2 ^ P * B := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num)] at hσ
    have hσ1 : |σ| ≤ 1 := abs_le.mpr ⟨hσ.1.le, hσ.2⟩
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    have h1 := abs_pR_le (P := P) pc hσ1
    have h2 := taylor_cos N (2 * π * x * T σ)
    have hTb : 0 ≤ T σ ∧ T σ ≤ 5502 / 10000 := piece_t_bounds hlt.le hhi hσ1
    have h3a : |2 * π * x * T σ| ≤ 2 * π * (5502 / 10000) * (5502 / 10000) := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_nonneg hTb.1]
      have hxT := mul_le_mul hx hTb.2 hTb.1 (by norm_num : (0 : ℝ) ≤ 5502 / 10000)
      have h2p : 0 < 2 * π := by positivity
      calc 2 * π * |x| * T σ = 2 * π * (|x| * T σ) := by ring
        _ ≤ 2 * π * ((5502 / 10000) * (5502 / 10000)) := mul_le_mul_of_nonneg_left hxT h2p.le
        _ = _ := by ring
    have h3 : |2 * π * x * T σ| ^ (2 * N) / ((2 * N).factorial : ℝ) ≤ B := by
      rw [hB]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h3a _) (by positivity)
    have h2' : |Real.cos (2 * π * x * T σ) - g σ| ≤ B := h2.trans h3
    exact mul_le_mul h1 h2' (abs_nonneg _) (by positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, show |(1 : ℝ) - -1| = 2 by norm_num] at this
  rw [abs_mul, abs_mul, abs_two, abs_of_pos he]
  have h4 : 0 ≤ 2 * peR pc := by positivity
  calc 2 * (peR pc * |∫ σ in (-1 : ℝ)..1, (pR P pc σ * Real.cos (2 * π * x * T σ) - pR P pc σ * g σ)|)
      = 2 * peR pc * |∫ σ in (-1 : ℝ)..1, (pR P pc σ * Real.cos (2 * π * x * T σ) - pR P pc σ * g σ)| := by ring
    _ ≤ 2 * peR pc * ((pmaxOne pc : ℝ) / 2 ^ P * B * 2) := mul_le_mul_of_nonneg_left this h4
    _ = _ := by ring

/-- `|P̂(x) - Σ_{n<N} (-1)^n (2πx)^{2n} μ_{2n}/(2n)!| ≤ 2r Pmax (2πr²)^{2N}/(2N)!` for `|x| ≤ r`. -/
theorem phat_cos_err {ps : List PPiece} (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1)
    {x : ℝ} (hx : |x| ≤ 5502 / 10000) (N : ℕ) :
    |PhatS P ps x - ∑ n ∈ range N, fcos n * x ^ (2 * n) * muR P ps (2 * n)| ≤
      2 * (5502 / 10000) * ((pmaxHi ps : ℝ) / 2 ^ P) *
        ((2 * π * (5502 / 10000) * (5502 / 10000)) ^ (2 * N) / ((2 * N).factorial : ℝ)) := by
  set B : ℝ := (2 * π * (5502 / 10000) * (5502 / 10000)) ^ (2 * N) / ((2 * N).factorial : ℝ) with hB
  have hB0 : 0 ≤ B := by positivity
  have hbnd := chain_bounds 0 ps hch hord
  have e1 : ∑ n ∈ range N, fcos n * x ^ (2 * n) * muR P ps (2 * n) =
      (ps.map fun pc => ∑ n ∈ range N, fcos n * x ^ (2 * n) *
        (2 * (peR pc * ∫ σ in (-1 : ℝ)..1, pR P pc σ * (pcR pc + peR pc * σ) ^ (2 * n)))).sum := by
    rw [← sum_range_listSum]
    refine sum_congr rfl (fun n _ => ?_)
    rw [muR, ← List.sum_map_mul_left]
  rw [e1, PhatS]
  refine (abs_listSum_sub_le _ _ ps).trans ?_
  refine (listSum_le_listSum ps (g := fun pc => 2 * peR pc * (2 * ((pmaxHi ps : ℝ) / 2 ^ P * B)))
    (fun pc hpc => ?_)).trans (le_of_eq ?_)
  · refine (piece_cos_err (hord pc hpc) (hbnd pc hpc).2 hx N).trans ?_
    have := pmaxOne_le_pmaxHi ps pc hpc
    have h5 : (pmaxOne pc : ℝ) ≤ pmaxHi ps := by exact_mod_cast this
    have := peR_nonneg pc
    gcongr
  · rw [List.sum_map_mul_right, chain_width_sum 0 ps hch hord]
    push_cast; ring

/-- `rhoOK`: `|P̂(x) - ψ(x)| + 2rε ≤ δ` for `|x| ≤ r`. -/
theorem rhoOK_sound {N : ℕ} {psi : List (ℤ × ℕ)} {ps : List PPiece} {eps delta : ℕ}
    (h : rhoOK P N psi ps eps delta = true) (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1)
    (hpsi : ∀ q ∈ psi, 0 < q.2) {x : ℝ} (hx : |x| ≤ 5502 / 10000) :
    |PhatS P ps x - Tpoly (psiR psi) 0 x| + 2 * (5502 / 10000) * ((eps : ℝ) / 2 ^ P) ≤ (delta : ℝ) / 2 ^ P := by
  unfold rhoOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlenpsi, _⟩, hsum⟩ := h
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hr : mem P (5502 / 10000 : ℝ) (ofRat P 2751 5000) := by
    have := mem_ofRat P 2751 5000 (by norm_num)
    convert this using 1; norm_num
  have h2pi : mem P (2 * π) (mulInt 2 (piB P)) := by
    have := mem_mulInt 2 (mem_piB P); simpa using this
  have htp2 := mem_mul h2pi h2pi
  have hqs : ∀ i, mem P (qR psi (0 + i)) ((psi.map fun q => ofRat P q.1 q.2).getD i ⟨0, 0⟩) := by
    intro i
    rw [zero_add]
    by_cases hi : i < psi.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
      unfold qR
      rw [List.getD_eq_getElem _ _ hi]
      exact mem_ofRat P _ _ (hpsi _ (List.getElem_mem hi))
    · push Not at hi
      rw [List.getD_eq_default _ _ (by simpa using hi)]
      unfold qR
      rw [List.getD_eq_default _ _ hi]
      simpa using mem_zero_ball (P := P)
  have hmu : MemL P ((List.range (2 * N)).map fun i => muR P ps (2 * 0 + i)) (momAll P (2 * N) ps) := by
    simpa using memL_momAll (P := P) (2 * N) ps
  have hfac0 : mem P (fcos 0) (ofInt P 1) := by simpa [fcos] using mem_ofInt P 1
  have hR := memL_rhoCoefAux htp2 (muR P ps) (qR psi) N 0 hfac0 hmu hqs
  simp only [zero_add] at hR
  set ρ : ℕ → ℝ := fun n => fcos n * muR P ps (2 * n) - qR psi n with hρ
  -- the three bounds
  have hS := sum_abs_mul_le hR (memL_map_same (fun n => mem_powB (mem_mul hr hr) n) (List.range N))
  rw [zipWith_range, listSum_range] at hS
  have hEN := abs_le_absHi (mem_mul (mem_mul (mem_mulInt 2 hr) (mem_point P (pmaxHi ps : ℤ)))
    (mem_divNat (d := fact (2 * N)) (by rw [fact_eq]; positivity) (mem_powB (mem_mul h2pi (mem_mul hr hr)) (2 * N))))
  have h2e := abs_le_absHi (mem_mul (mem_mulInt 2 hr) (mem_point P (eps : ℤ)))
  -- the analytic part
  have hcos := phat_cos_err (P := P) hch hord hx N
  have hpsiE := Tpoly_psiR psi N hlenpsi x
  have hsplit : PhatS P ps x - Tpoly (psiR psi) 0 x =
      (PhatS P ps x - ∑ n ∈ range N, fcos n * x ^ (2 * n) * muR P ps (2 * n)) + ∑ n ∈ range N, ρ n * x ^ (2 * n) := by
    rw [hpsiE, hρ]
    simp only [sub_mul]
    rw [sum_sub_distrib]
    have : ∑ n ∈ range N, fcos n * muR P ps (2 * n) * x ^ (2 * n) =
        ∑ n ∈ range N, fcos n * x ^ (2 * n) * muR P ps (2 * n) := sum_congr rfl (fun n _ => by ring)
    rw [this]; ring
  have hρb : |∑ n ∈ range N, ρ n * x ^ (2 * n)| ≤ ∑ n ∈ range N, |ρ n| * (5502 / 10000 * (5502 / 10000)) ^ n := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun n _ => ?_))
    rw [abs_mul, abs_pow, pow_mul]
    gcongr
    rw [sq_abs, ← sq]
    have : |x| ^ 2 ≤ (5502 / 10000) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at this; exact this
  have hENr : 2 * (5502 / 10000) * ((pmaxHi ps : ℝ) / 2 ^ P) *
      ((2 * π * (5502 / 10000) * (5502 / 10000)) ^ (2 * N) / ((2 * N).factorial : ℝ)) ≤
      ((mul P (mul P (mulInt 2 (ofRat P 2751 5000)) ⟨(pmaxHi ps : ℤ), 0⟩)
        (divNat (fact (2 * N)) (powB P (mul P (mulInt 2 (piB P)) (mul P (ofRat P 2751 5000) (ofRat P 2751 5000)))
          (2 * N)))).absHi : ℝ) / 2 ^ P := by
    refine le_trans (le_of_eq ?_) ((le_abs_self _).trans hEN)
    rw [fact_eq]; push_cast; ring
  have h2er : 2 * (5502 / 10000) * ((eps : ℝ) / 2 ^ P) ≤
      ((mul P (mulInt 2 (ofRat P 2751 5000)) ⟨(eps : ℤ), 0⟩).absHi : ℝ) / 2 ^ P := by
    refine le_trans (le_of_eq ?_) ((le_abs_self _).trans h2e)
    push_cast; ring
  have hsumR := (Nat.cast_le (α := ℝ)).mpr hsum
  rw [Nat.cast_add, Nat.cast_add] at hsumR
  have hsumR' := div_le_div_of_nonneg_right hsumR hP.le
  rw [add_div, add_div] at hsumR'
  rw [hsplit]
  have := abs_add_le (PhatS P ps x - ∑ n ∈ range N, fcos n * x ^ (2 * n) * muR P ps (2 * n))
    (∑ n ∈ range N, ρ n * x ^ (2 * n))
  linarith

end SignUnc.Chk
