import SignUnc.LowSound1

/-!
# Soundness of the lower checker, part 2: omitted terms of `v`, the approximant `P` (`pieceP_OK`)
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex Finset

variable {P : ℕ}

/-! ## The omitted terms of `v` (signed pairs) -/

/-- `Σ c (b - b̂)` over a list of triples `(a, s, c)`. -/
noncomputable def vsum (L : List (ℝ × ℝ × ℝ)) (x : ℝ) : ℝ := (L.map fun q => q.2.2 * (gb q.1 q.2.1 x - gbh q.1 q.2.1 x)).sum

theorem vsum_append (L1 L2 : List (ℝ × ℝ × ℝ)) (x : ℝ) : vsum (L1 ++ L2) x = vsum L1 x + vsum L2 x := by
  simp [vsum, List.map_append, List.sum_append]

theorem vsum_triples (g : GGroup) (y : ℝ) :
    vsum g.triples y = ∑ k ∈ range g.cs.length, cK g k * (gb (aR g) (sR g k) y - gbh (aR g) (sR g k) y) := by
  rw [vsum, GGroup.triples, List.map_map]
  exact sum_map_csR_all g (fun r => r.1 * (gb (aR g) r.2 y - gbh (aR g) r.2 y))

theorem tauSum_inclHV_zero (g : GGroup) (sp : GSpec) (y : ℝ) :
    tauSum (inclHV g sp) 0 y =
      if sp.hz then -∑ k ∈ range g.cs.length, cK g k * gbh (aR g) (sR g k) y else 0 := by
  unfold inclHV
  split_ifs with hz
  · rw [tauSum_eq, List.map_map]
    simp only [Function.comp_def]
    rw [sum_map_csR_all g (fun r => tauQ (quadH (aR g) (-r.1) r.2) 0 y), ← sum_neg_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    rw [tau_quadH]
    simp [pw2R, gbh]
    ring
  · simp [tauSum]

theorem omitGV_sound {n : ℕ} {G : PG} (hG : PGOk P G) {sp : GSpec} {ylo yhi : ℤ} {R : ℕ}
    (h : omitG P n G sp ylo yhi = some R) {y : ℝ} (hy1 : (ylo : ℝ) / 2 ^ P ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ P) :
    |vsum G.g.triples y - tauSum (inclV G.g sp) 0 y| ≤ (R : ℝ) / 2 ^ P := by
  unfold omitG at h
  by_cases hc : 0 ≤ ylo ∧ sp.k1 ≤ sp.k2 ∧ sp.k2 ≤ G.g.cs.length ∧ sp.kF ≤ G.g.cs.length
  swap
  · simp only [hc, if_false] at h
    exact absurd h (by simp)
  obtain ⟨hylo, h12, h2N, hFN⟩ := hc
  simp only [hylo, h12, h2N, hFN, and_self, if_true, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨ta, hta, tb, htb, tc, htc, td, htd, rfl⟩ := h
  set g := G.g
  set N := g.cs.length
  set a := aR g
  set cm : ℝ := (cmaxHi G : ℝ) / 2 ^ P
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hA : ∑ k ∈ range sp.k1, Real.exp (-π * a * (y - sR g k) ^ 2) ≤ (ta : ℝ) / 2 ^ P := by
    split_ifs at hta with hk
    · exact low_tail hG hk hta hy1
    · simp only [Option.some.injEq] at hta; subst hta
      have : sp.k1 = 0 := by omega
      simp [this]
  have hB : ∑ k ∈ Ico sp.k2 N, Real.exp (-π * a * (y - sR g k) ^ 2) ≤ (tb : ℝ) / 2 ^ P := by
    split_ifs at htb with hk
    · exact high_tail hG htb hy2 N
    · simp only [Option.some.injEq] at htb; subst htb
      have : N ≤ sp.k2 := by omega
      simp [Ico_eq_empty_of_le this]
  have hC : ∑ k ∈ Ico sp.kF N, Real.exp (-π * a * (y + sR g k) ^ 2) ≤ (tc : ℝ) / 2 ^ P := by
    split_ifs at htc with hk
    · exact f_tail hG htc hy1 N
    · simp only [Option.some.injEq] at htc; subst htc
      have : N ≤ sp.kF := by omega
      simp [Ico_eq_empty_of_le this]
  have hD' : |if sp.hz then (0 : ℝ) else ∑ k ∈ range N, cK g k * gbh a (sR g k) y| ≤ (td : ℝ) / 2 ^ P := by
    split_ifs at htd with hz
    · simp only [Option.some.injEq] at htd; subst htd; simp [hz]
    · simp only [Option.map_eq_some_iff] at htd
      obtain ⟨e, he, rfl⟩ := htd
      simp only [hz, if_false]
      exact h_omit hG hylo he hy1
  have hsplit : vsum g.triples y - tauSum (inclV g sp) 0 y =
      ∑ k ∈ range sp.k1, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
      ∑ k ∈ Ico sp.k2 N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
      ∑ k ∈ Ico sp.kF N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) -
      (if sp.hz then (0 : ℝ) else ∑ k ∈ range N, cK g k * gbh a (sR g k) y) := by
    rw [vsum_triples, inclV, tauSum_append, tauSum_append, tauSum_inclE_zero g sp h12 h2N,
      tauSum_inclF_zero g sp hFN, tauSum_inclHV_zero]
    have eE : ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) =
        ∑ k ∈ range sp.k1, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
        ∑ k ∈ Ico sp.k1 sp.k2, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
        ∑ k ∈ Ico sp.k2 N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) := by
      rw [sum_range_add_sum_Ico _ h12, sum_range_add_sum_Ico _ h2N]
    have eF : ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) =
        ∑ k ∈ range sp.kF, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) +
        ∑ k ∈ Ico sp.kF N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) := by
      rw [sum_range_add_sum_Ico _ hFN]
    have eT : ∑ k ∈ range N, cK g k * (gb a (sR g k) y - gbh a (sR g k) y) =
        ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
        ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) -
        ∑ k ∈ range N, cK g k * gbh a (sR g k) y := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl (fun k _ => ?_)
      unfold gb; ring
    rw [eT, eE, eF]
    split_ifs <;> ring
  rw [hsplit]
  have hk1 : ∀ k ∈ range sp.k1, k < N := fun k hk => by simp at hk; omega
  have hk2 : ∀ k ∈ Ico sp.k2 N, k < N := fun k hk => by simp at hk; omega
  have hkF : ∀ k ∈ Ico sp.kF N, k < N := fun k hk => by simp at hk; omega
  have b1 := abs_sum_cK_le hG _ hk1 (fun k => Real.exp (-π * a * (y - sR g k) ^ 2)) (fun _ => (Real.exp_pos _).le)
  have b2 := abs_sum_cK_le hG _ hk2 (fun k => Real.exp (-π * a * (y - sR g k) ^ 2)) (fun _ => (Real.exp_pos _).le)
  have b3 := abs_sum_cK_le hG _ hkF (fun k => Real.exp (-π * a * (y + sR g k) ^ 2)) (fun _ => (Real.exp_pos _).le)
  have hcm : 0 ≤ cm := by positivity
  have hfin : cm * (((ta + tb + tc : ℕ) : ℝ) / 2 ^ P) ≤ ((cdiv (cmaxHi G * (ta + tb + tc)) (2 ^ P) : ℕ) : ℝ) / 2 ^ P := by
    have hc := cdiv_spec (cmaxHi G * (ta + tb + tc)) (2 ^ P) (by positivity)
    push_cast at hc ⊢
    have : (cmaxHi G : ℝ) / 2 ^ P * (((ta : ℝ) + tb + tc) / 2 ^ P) =
        ((cmaxHi G : ℝ) * ((ta : ℝ) + tb + tc) / 2 ^ P) / 2 ^ P := by ring
    rw [this]; gcongr
  set A := ∑ k ∈ range sp.k1, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) with hAdef
  set B := ∑ k ∈ Ico sp.k2 N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) with hBdef
  set C := ∑ k ∈ Ico sp.kF N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) with hCdef
  set D := (if sp.hz then (0 : ℝ) else ∑ k ∈ range N, cK g k * gbh a (sR g k) y) with hDdef
  have t1 := abs_sub (A + B + C) D
  have t2 := abs_add_le (A + B) C
  have t3 := abs_add_le A B
  have hA' : |A| ≤ cm * ((ta : ℝ) / 2 ^ P) := le_trans b1 (mul_le_mul_of_nonneg_left hA hcm)
  have hB' : |B| ≤ cm * ((tb : ℝ) / 2 ^ P) := le_trans b2 (mul_le_mul_of_nonneg_left hB hcm)
  have hC' : |C| ≤ cm * ((tc : ℝ) / 2 ^ P) := le_trans b3 (mul_le_mul_of_nonneg_left hC hcm)
  have hsum : cm * ((ta : ℝ) / 2 ^ P) + cm * ((tb : ℝ) / 2 ^ P) + cm * ((tc : ℝ) / 2 ^ P) =
      cm * (((ta + tb + tc : ℕ) : ℝ) / 2 ^ P) := by push_cast; ring
  have hlast : (((cdiv (cmaxHi G * (ta + tb + tc)) (2 ^ P) + td : ℕ) : ℝ)) / 2 ^ P =
      ((cdiv (cmaxHi G * (ta + tb + tc)) (2 ^ P) : ℕ) : ℝ) / 2 ^ P + (td : ℝ) / 2 ^ P := by push_cast; ring
  rw [hlast]
  linarith

theorem omitAllV_sound {n : ℕ} {ylo yhi : ℤ} {y : ℝ} (hy1 : (ylo : ℝ) / 2 ^ P ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ P) :
    ∀ {gs : List GGroup} {pgs : List PG4} {sps : List GSpec} {R : ℕ},
      List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs →
      omitAll P n ylo yhi pgs sps = some R →
      |vsum (gs.flatMap GGroup.triples) y - tauSum (inclAllV gs sps) 0 y| ≤ (R : ℝ) / 2 ^ P
  | [], [], [], R, List.Forall₂.nil, h => by
    simp only [omitAll, Option.some.injEq] at h
    subst h
    simp [vsum, inclAllV, tauSum]
  | [], [], _ :: _, R, List.Forall₂.nil, h => by simp [omitAll] at h
  | _ :: _, _ :: _, [], R, List.Forall₂.cons _ _, h => by simp [omitAll] at h
  | g :: gs, G :: pgs, sp :: sps, R, List.Forall₂.cons hG hgs, h => by
    simp only [omitAll, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    have h1 := omitGV_sound hG.1.hG ha hy1 hy2
    rw [hG.2] at h1
    have h2 := omitAllV_sound hy1 hy2 hgs hb
    rw [List.flatMap_cons, vsum_append, inclAllV, tauSum_append]
    have e : vsum g.triples y + vsum (gs.flatMap GGroup.triples) y - (tauSum (inclV g sp) 0 y + tauSum (inclAllV gs sps) 0 y) =
        (vsum g.triples y - tauSum (inclV g sp) 0 y) + (vsum (gs.flatMap GGroup.triples) y - tauSum (inclAllV gs sps) 0 y) := by
      ring
    rw [e]
    calc _ ≤ |vsum g.triples y - tauSum (inclV g sp) 0 y| + |vsum (gs.flatMap GGroup.triples) y - tauSum (inclAllV gs sps) 0 y| :=
          abs_add_le _ _
      _ ≤ (a : ℝ) / 2 ^ P + (b : ℝ) / 2 ^ P := add_le_add h1 h2
      _ = ((a + b : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

/-! ## Scaling and coefficient comparison -/

theorem memL_scaleRatAux {w d : ℕ} (hd : 0 < d) {xR : ℕ → ℝ} :
    ∀ (N j : ℕ) {T : List Ball}, MemL P ((List.range' j N).map xR) T →
      MemL P ((List.range' j N).map fun i => xR i * ((w : ℝ) / d) ^ i) (scaleRatAux w d j T)
  | 0, _, T, h => by cases h; simp [scaleRatAux]
  | N + 1, j, T, h => by
    rw [List.range'_succ, List.map_cons] at h
    cases h with
    | cons hx hT =>
      rw [List.range'_succ, List.map_cons]
      simp only [scaleRatAux]
      refine List.Forall₂.cons ?_ (memL_scaleRatAux hd N (j + 1) hT)
      have := mem_divNat (pow_pos hd j) (mem_mulInt ((w ^ j : ℕ) : ℤ) hx)
      convert this using 1
      push_cast; rw [div_pow]; ring

theorem memL_scaleRat {w d : ℕ} (hd : 0 < d) {xR : ℕ → ℝ} {N : ℕ} {T : List Ball}
    (h : MemL P ((List.range N).map xR) T) :
    MemL P ((List.range N).map fun i => xR i * ((w : ℝ) / d) ^ i) (scaleRat w d T) := by
  rw [List.range_eq_range'] at h ⊢
  exact memL_scaleRatAux hd N 0 h

theorem listSum_map_getD {α : Type*} (dflt : α) (g : α → ℕ) :
    ∀ l : List α, (((l.map g).sum : ℕ) : ℝ) = ∑ i ∈ range l.length, ((g (l.getD i dflt) : ℕ) : ℝ)
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.sum_cons, Nat.cast_add, listSum_map_getD dflt g l, List.length_cons, sum_range_succ']
    simp [add_comm]

/-- `|Σ_{j ≤ m} b_j σ^j - Σ_{i ≤ D} (B_i/2^P) σ^i| ≤ (S₁ + S₂)/2^P` for `|σ| ≤ 1`. -/
theorem coef_compare {m D : ℕ} (hDm : D ≤ m) {bR : ℕ → ℝ} {bs : List Ball}
    (hb : MemL P ((List.range (m + 1)).map bR) bs) {B : List ℤ} (hB : B.length = D + 1) {σ : ℝ} (hσ : |σ| ≤ 1) :
    |∑ j ∈ range (m + 1), bR j * σ ^ j - ∑ i ∈ range (D + 1), ((B.getD i 0 : ℤ) : ℝ) / 2 ^ P * σ ^ i| ≤
      ((((List.zipWith (fun b B => sub b ⟨B, 0⟩) bs B).map absHi).sum +
        ((bs.drop (D + 1)).map absHi).sum : ℕ) : ℝ) / 2 ^ P := by
  have hlen : bs.length = m + 1 := by have := hb.length_eq; simp at this; omega
  have hget : ∀ i (hi : i < m + 1), mem P (bR i) (bs.getD i ⟨0, 0⟩) := by
    intro i hi
    have := hb.get (i := i) (by simpa using hi) (by rw [hlen]; exact hi)
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at this
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
    exact this
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hσj : ∀ j : ℕ, |σ ^ j| ≤ 1 := fun j => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hσ
  rw [← sum_range_add_sum_Ico _ (by omega : D + 1 ≤ m + 1)]
  have e : ∑ j ∈ range (D + 1), bR j * σ ^ j + ∑ j ∈ Ico (D + 1) (m + 1), bR j * σ ^ j -
      ∑ i ∈ range (D + 1), ((B.getD i 0 : ℤ) : ℝ) / 2 ^ P * σ ^ i =
      ∑ i ∈ range (D + 1), (bR i - ((B.getD i 0 : ℤ) : ℝ) / 2 ^ P) * σ ^ i + ∑ j ∈ Ico (D + 1) (m + 1), bR j * σ ^ j := by
    have : ∑ i ∈ range (D + 1), (bR i - ((B.getD i 0 : ℤ) : ℝ) / 2 ^ P) * σ ^ i =
        ∑ i ∈ range (D + 1), bR i * σ ^ i - ∑ i ∈ range (D + 1), ((B.getD i 0 : ℤ) : ℝ) / 2 ^ P * σ ^ i := by
      rw [← sum_sub_distrib]; refine sum_congr rfl (fun i _ => ?_); ring
    rw [this]; ring
  rw [e]
  -- the two list sums as index sums
  have hz : (List.zipWith (fun b B => sub b ⟨B, 0⟩) bs B).length = D + 1 := by simp [hlen, hB]; omega
  have hS1 : ((((List.zipWith (fun b B => sub b ⟨B, 0⟩) bs B).map absHi).sum : ℕ) : ℝ) =
      ∑ i ∈ range (D + 1), ((sub (bs.getD i ⟨0, 0⟩) ⟨B.getD i 0, 0⟩).absHi : ℝ) := by
    rw [listSum_map_getD (⟨0, 0⟩ : Ball) absHi, hz]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' : i < D + 1 := by simpa using hi
    rw [List.getD_eq_getElem _ _ (by rw [hz]; exact hi'), List.getElem_zipWith,
      List.getD_eq_getElem _ _ (by rw [hlen]; omega), List.getD_eq_getElem _ _ (by rw [hB]; exact hi')]
  have hS2 : ((((bs.drop (D + 1)).map absHi).sum : ℕ) : ℝ) = ∑ j ∈ Ico (D + 1) (m + 1), ((bs.getD j ⟨0, 0⟩).absHi : ℝ) := by
    rw [listSum_map_getD (⟨0, 0⟩ : Ball) absHi, List.length_drop, hlen, sum_Ico_eq_sum_range,
      show m + 1 - (D + 1) = m + 1 - (D + 1) from rfl]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' : i < m + 1 - (D + 1) := by simpa using hi
    rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega), List.getElem_drop,
      List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
  rw [Nat.cast_add, hS1, hS2, add_div, sum_div, sum_div]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i hi => ?_))
    have hi' : i < D + 1 := by simpa using hi
    rw [abs_mul]
    have hm := abs_le_absHi (mem_sub (hget i (by omega)) (mem_point' P (B.getD i 0)))
    calc |bR i - ((B.getD i 0 : ℤ) : ℝ) / 2 ^ P| * |σ ^ i| ≤ |bR i - ((B.getD i 0 : ℤ) : ℝ) / 2 ^ P| * 1 :=
          mul_le_mul_of_nonneg_left (hσj i) (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hm
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j hj => ?_))
    have hj' : j < m + 1 := by simp at hj; omega
    rw [abs_mul]
    have hm := abs_le_absHi (hget j hj')
    calc |bR j| * |σ ^ j| ≤ |bR j| * 1 := mul_le_mul_of_nonneg_left (hσj j) (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hm

/-! ## The pieces of `P` -/

/-- The piece polynomial `P_k(t) = Σ_i (B_i/2^P) ((t - c)/η)^i`, `c = (lo+hi)/20000`, `η = (hi-lo)/20000`. -/
noncomputable def Peval (P : ℕ) (pc : PPiece) (t : ℝ) : ℝ :=
  ∑ i ∈ range pc.2.2.length, ((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P *
    ((t - ((pc.1 + pc.2.1 : ℕ) : ℝ) / 20000) / (((pc.2.1 - pc.1 : ℕ) : ℝ) / 20000)) ^ i

theorem memL_getD {f : ℕ → ℝ} {N : ℕ} {L : List Ball} (h : MemL P ((List.range N).map f) L) {i : ℕ} (hi : i < N) :
    mem P (f i) (L.getD i ⟨0, 0⟩) := by
  have hlen : L.length = N := by have := h.length_eq; simp at this; omega
  have := h.get (i := i) (by simpa using hi) (by rw [hlen]; exact hi)
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at this
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
  exact this

theorem mem_widen {c η x : ℝ} {C E : Ball} (hc : mem P c C) (hη : mem P η E) (hx : |x - c| ≤ η) :
    mem P x ⟨C.m, C.r + E.m.natAbs + E.r⟩ := by
  unfold mem at hc hη ⊢
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have h1 : η ≤ (E.m.natAbs : ℝ) / 2 ^ P + (E.r : ℝ) / 2 ^ P := by
    have := (abs_le.mp hη).2
    have hm : (E.m : ℝ) ≤ (E.m.natAbs : ℝ) := by
      rw [Nat.cast_natAbs]; exact_mod_cast le_abs_self E.m
    have : (E.m : ℝ) / 2 ^ P ≤ (E.m.natAbs : ℝ) / 2 ^ P := div_le_div_of_nonneg_right hm hP.le
    linarith
  calc |x - (C.m : ℝ) / 2 ^ P| ≤ |x - c| + |c - (C.m : ℝ) / 2 ^ P| := abs_sub_le _ _ _
    _ ≤ η + (C.r : ℝ) / 2 ^ P := add_le_add hx hc
    _ ≤ ((C.r + E.m.natAbs + E.r : ℕ) : ℝ) / 2 ^ P := by push_cast; rw [add_div, add_div]; linarith

theorem absHi_scale_bound {T' : Ball} {w d : ℕ} (hd : 0 < d) (N : ℕ) :
    (T'.absHi : ℝ) / 2 ^ P * ((w : ℝ) / d) ^ N ≤
      ((divNat (d ^ N) (mulInt ((w ^ N : ℕ) : ℤ) (absB T'))).absHi : ℝ) / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have h0 : mem P ((T'.absHi : ℝ) / 2 ^ P) (absB T') := by
    unfold mem absB absHi
    simp only [Int.cast_natCast]
    rw [show ((T'.m.natAbs + T'.r : ℕ) : ℝ) / 2 ^ P - ((T'.m.natAbs : ℕ) : ℝ) / 2 ^ P = (T'.r : ℝ) / 2 ^ P by
      push_cast; ring]
    rw [abs_of_nonneg (by positivity)]
  have h1 := mem_divNat (pow_pos hd N) (mem_mulInt ((w ^ N : ℕ) : ℤ) h0)
  have h2 := abs_le_absHi h1
  have e : (((w ^ N : ℕ) : ℤ) : ℝ) * ((T'.absHi : ℝ) / 2 ^ P) / ((d ^ N : ℕ) : ℝ) =
      (T'.absHi : ℝ) / 2 ^ P * ((w : ℝ) / d) ^ N := by push_cast; rw [div_pow]; ring
  rw [e] at h2
  exact le_trans (le_abs_self _) h2

theorem pieceP_OK_sound {n k D L : ℕ} {gs : List GGroup} {pgs : List PG4}
    (hgs : List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs) {sps : List GSpec}
    {cos : List (ℕ × ℕ × ℤ × ℕ)} (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2)
    {psi : List (ℤ × ℕ)} (hpsi : ∀ q ∈ psi, 0 < q.2) {eps R : ℕ} {pc : PPiece}
    (h : pieceP_OK P n k D L pgs sps cos (psiPoly P psi) eps R pc = true) {t : ℝ}
    (ht1 : ((pc.1 : ℕ) : ℝ) / 10000 ≤ t) (ht2 : t ≤ ((pc.2.1 : ℕ) : ℝ) / 10000) :
    |Tphi gs sps cos psi 0 t - Peval P pc t| + (R : ℝ) / 2 ^ P ≤ (eps : ℝ) / 2 ^ P := by
  unfold pieceP_OK at h
  set C := pcen P pc with hCdef
  set E := peta P pc with hEdef
  set w := pc.2.1 - pc.1 with hwdef
  rcases hA : phiJet P (D + L) (expB' P n) (cosSinTurn P n k) pgs sps cos (psiPoly P psi) C with _ | T
  · simp [hA] at h
  rcases hB : phiJet P (D + L + 1) (expH P n) (cosSinTurnC P n k) pgs sps cos (psiPoly P psi)
      ⟨C.m, C.r + E.m.natAbs + E.r⟩ with _ | T'
  · simp [hA, hB] at h
  simp only [hA, hB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlt, hTlen⟩, hBlen⟩, hle⟩ := h
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  set c : ℝ := ((pc.1 + pc.2.1 : ℕ) : ℝ) / 20000 with hcdef
  set η : ℝ := ((pc.2.1 - pc.1 : ℕ) : ℝ) / 20000 with hηdef
  have hw0 : (0 : ℝ) < (w : ℝ) := by rw [hwdef]; exact_mod_cast Nat.sub_pos_of_lt hlt
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hc : mem P c C := by
    have := mem_ofRat P ((pc.1 + pc.2.1 : ℕ) : ℤ) 20000 (by norm_num)
    rw [hCdef]; unfold pcen; simpa [c] using this
  have hη : mem P η E := by
    have := mem_ofRat P ((pc.2.1 - pc.1 : ℕ) : ℤ) 20000 (by norm_num)
    rw [hEdef]; unfold peta; simpa [η] using this
  have hcη1 : c - η = ((pc.1 : ℕ) : ℝ) / 10000 := by
    rw [hcdef, hηdef]; push_cast [Nat.cast_sub hlt.le]; ring
  have hcη2 : c + η = ((pc.2.1 : ℕ) : ℝ) / 10000 := by
    rw [hcdef, hηdef]; push_cast [Nat.cast_sub hlt.le]; ring
  have hex : ∀ {x : ℝ} {X Ee : Ball}, mem P x X → expB' P n X = some Ee → mem P (Real.exp x) Ee :=
    fun hx he => mem_expB' hx he
  have hcz : ∀ {u : ℝ} {U C' S : Ball}, mem P u U → cosSinTurn P n k U = some (C', S) →
      mem P (Real.cos (2 * π * u)) C' ∧ mem P (Real.sin (2 * π * u)) S := fun hu h => mem_cosSinTurn hu h
  have hexH : ∀ {x : ℝ} {X Ee : Ball}, mem P x X → expH P n X = some Ee → mem P (Real.exp x) Ee :=
    fun hx he => mem_expH hx he
  have hczC : ∀ {u : ℝ} {U C' S : Ball}, mem P u U → cosSinTurnC P n k U = some (C', S) →
      mem P (Real.cos (2 * π * u)) C' ∧ mem P (Real.sin (2 * π * u)) S := fun hu h => mem_cosSinTurnC hu h
  have hT := memL_phiJet hex hcz hc hgs hcos hpsi hA
  -- the remainder bound on the piece
  set M : ℝ := ((T'.getD (D + L + 1) ⟨0, 0⟩).absHi : ℝ) / 2 ^ P with hMdef
  have hM : ∀ x ∈ Set.Icc (c - η) (c + η), |Tphi gs sps cos psi (D + L + 1) x| ≤ M := by
    intro x hx
    have hxb : |x - c| ≤ η := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hT' := memL_phiJet hexH hczC (mem_widen hc hη hxb) hgs hcos hpsi hB
    exact abs_le_absHi (memL_getD hT' (by omega))
  have hchain : ∀ j ≤ D + L, ∀ x, HasDerivAt (Tphi gs sps cos psi j) (((j : ℝ) + 1) * Tphi gs sps cos psi (j + 1) x) x :=
    fun j _ x => hasDerivAt_Tphi gs sps cos psi j x
  have ht : t ∈ Set.Icc (c - η) (c + η) := ⟨by rw [hcη1]; exact ht1, by rw [hcη2]; exact ht2⟩
  have htay := taylorK hchain hM t ht
  have htc : |t - c| ≤ η := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the Taylor polynomial in the scaled variable
  set σ := (t - c) / η with hσdef
  have hσ : |σ| ≤ 1 := by rw [hσdef, abs_div, abs_of_pos hη0]; exact (div_le_one hη0).mpr htc
  have hbs := memL_scaleRat (w := w) (d := 20000) (by norm_num) hT
  have hwη : (w : ℝ) / ((20000 : ℕ) : ℝ) = η := by rw [hηdef, hwdef]; norm_num
  rw [hwη] at hbs
  have hnp : npoly (Tphi gs sps cos psi) c (D + L) t =
      ∑ j ∈ range (D + L + 1), Tphi gs sps cos psi j c * η ^ j * σ ^ j := by
    unfold npoly
    refine sum_congr rfl (fun j _ => ?_)
    have hηne : η ≠ 0 := hη0.ne'
    have e : η ^ j * ((t - c) / η) ^ j = (t - c) ^ j := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hσdef, mul_assoc, e]
  have hcmp := coef_compare (P := P) (m := D + L) (D := D) (by omega) hbs hBlen hσ
  have hPe : Peval P pc t = ∑ i ∈ range (D + 1), ((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P * σ ^ i := by
    unfold Peval; rw [hBlen]
  have hrem : M * |t - c| ^ (D + L + 1) ≤
      ((divNat (20000 ^ (D + L + 1)) (mulInt ((w ^ (D + L + 1) : ℕ) : ℤ)
        (absB (T'.getD (D + L + 1) ⟨0, 0⟩)))).absHi : ℝ) / 2 ^ P := by
    have h1 := absHi_scale_bound (P := P) (T' := T'.getD (D + L + 1) ⟨0, 0⟩) (w := w) (d := 20000) (by norm_num) (D + L + 1)
    rw [hwη] at h1
    have hM0 : 0 ≤ M := by positivity
    calc M * |t - c| ^ (D + L + 1) ≤ M * η ^ (D + L + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) htc _) hM0
      _ ≤ _ := h1
  have hfin : (((((List.zipWith (fun b B => sub b ⟨B, 0⟩) (scaleRat w 20000 T) pc.2.2).map absHi).sum +
        (((scaleRat w 20000 T).drop (D + 1)).map absHi).sum : ℕ) : ℝ) / 2 ^ P) +
      ((divNat (20000 ^ (D + L + 1)) (mulInt ((w ^ (D + L + 1) : ℕ) : ℤ)
        (absB (T'.getD (D + L + 1) ⟨0, 0⟩)))).absHi : ℝ) / 2 ^ P + (R : ℝ) / 2 ^ P ≤ (eps : ℝ) / 2 ^ P := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hP.le
  rw [hnp] at htay
  rw [hPe]
  have e : |Tphi gs sps cos psi 0 t - ∑ i ∈ range (D + 1), ((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P * σ ^ i| ≤
      |Tphi gs sps cos psi 0 t - ∑ j ∈ range (D + L + 1), Tphi gs sps cos psi j c * η ^ j * σ ^ j| +
      |∑ j ∈ range (D + L + 1), Tphi gs sps cos psi j c * η ^ j * σ ^ j -
        ∑ i ∈ range (D + 1), ((pc.2.2.getD i 0 : ℤ) : ℝ) / 2 ^ P * σ ^ i| := abs_sub_le _ _ _
  linarith

end SignUnc.Chk
