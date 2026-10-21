import SignUnc.JetSound3

/-!
# Soundness of checker v4, part 4: included terms and the bound of the omitted terms (`omitG`, `omitAll`)

For a group `g` and a spec `sp`, `incl g sp` lists the included terms as quadratic exponentials (E-terms
`k ∈ [k1, k2)`, mirror terms `k < kF`, the cosine terms iff `hz`).  `omitG_sound`: on `[ylo, yhi]` (`0 ≤ ylo`),
`|gsum g.triples y - tauSum (incl g sp) 0 y| ≤ R / 2^P`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Finset

variable {P : ℕ}

/-! ## Included terms -/

noncomputable def inclE (g : GGroup) (sp : GSpec) : List (ℂ × ℂ × ℂ × ℂ) :=
  ((g.csR.drop sp.k1).take (sp.k2 - sp.k1)).map fun r => quadE (aR g) r.1 r.2

noncomputable def inclF (g : GGroup) (sp : GSpec) : List (ℂ × ℂ × ℂ × ℂ) :=
  (g.csR.take sp.kF).map fun r => quadF (aR g) r.1 r.2

noncomputable def inclH (g : GGroup) (sp : GSpec) : List (ℂ × ℂ × ℂ × ℂ) :=
  if sp.hz then g.csR.map fun r => quadH (aR g) r.1 r.2 else []

/-- The included terms of a group. -/
noncomputable def incl (g : GGroup) (sp : GSpec) : List (ℂ × ℂ × ℂ × ℂ) := inclE g sp ++ inclF g sp ++ inclH g sp

/-- The included terms of all groups. -/
noncomputable def inclAll : List GGroup → List GSpec → List (ℂ × ℂ × ℂ × ℂ)
  | g :: gs, sp :: sps => incl g sp ++ inclAll gs sps
  | _, _ => []

/-! ## Index form of the group sums -/

/-- The coefficient `c_k`. -/
noncomputable def cK (g : GGroup) (k : ℕ) : ℝ := cR (g.cs.getD k (0, 1))

theorem csR_getElem (g : GGroup) (k : ℕ) (hk : k < g.csR.length) : g.csR[k] = (cK g k, sR g k) := by
  have hk' : k < g.cs.length := by rwa [csR_length] at hk
  simp [GGroup.csR, cK]
  rw [List.getElem?_eq_getElem hk']
  rfl

theorem sum_map_csR (g : GGroup) (f : ℝ × ℝ → ℝ) (k1 : ℕ) :
    ∀ m, k1 + m ≤ g.cs.length → (((g.csR.drop k1).take m).map f).sum = ∑ k ∈ Ico k1 (k1 + m), f (cK g k, sR g k)
  | 0, _ => by simp
  | m + 1, h => by
    have hlt : k1 + m < g.csR.length := by rw [csR_length]; omega
    rw [List.take_succ, List.map_append, List.sum_append, sum_map_csR g f k1 m (by omega),
      show k1 + (m + 1) = (k1 + m) + 1 by omega, sum_Ico_succ_top (by omega)]
    congr 1
    rw [List.getElem?_drop, List.getElem?_eq_getElem hlt, csR_getElem g _ hlt]
    simp

theorem sum_map_csR_all (g : GGroup) (f : ℝ × ℝ → ℝ) :
    (g.csR.map f).sum = ∑ k ∈ range g.cs.length, f (cK g k, sR g k) := by
  have := sum_map_csR g f 0 g.cs.length (by omega)
  rw [List.drop_zero, List.take_of_length_le (by rw [csR_length])] at this
  rw [this, range_eq_Ico, zero_add]

theorem gsum_eq_sum (L : List (ℝ × ℝ × ℝ)) (x : ℝ) :
    gsum L x = (L.map fun q => q.2.2 * (gb q.1 q.2.1 x + gbh q.1 q.2.1 x)).sum := by
  induction L with
  | nil => simp [gsum]
  | cons q L ih => obtain ⟨a, s, c⟩ := q; simp [gsum, ih]

theorem gsum_triples (g : GGroup) (y : ℝ) :
    gsum g.triples y = ∑ k ∈ range g.cs.length, cK g k * (gb (aR g) (sR g k) y + gbh (aR g) (sR g k) y) := by
  rw [gsum_eq_sum, GGroup.triples, List.map_map]
  exact sum_map_csR_all g (fun r => r.1 * (gb (aR g) r.2 y + gbh (aR g) r.2 y))

theorem tauSum_inclE_zero (g : GGroup) (sp : GSpec) (h12 : sp.k1 ≤ sp.k2) (h2 : sp.k2 ≤ g.cs.length) (y : ℝ) :
    tauSum (inclE g sp) 0 y = ∑ k ∈ Ico sp.k1 sp.k2, cK g k * Real.exp (-π * aR g * (y - sR g k) ^ 2) := by
  rw [tauSum_eq, inclE, List.map_map]
  have := sum_map_csR g (fun r => tauQ (quadE (aR g) r.1 r.2) 0 y) sp.k1 (sp.k2 - sp.k1) (by omega)
  simp only [Function.comp_def]
  rw [this, show sp.k1 + (sp.k2 - sp.k1) = sp.k2 by omega]
  refine sum_congr rfl (fun k _ => ?_)
  rw [tau_quadE]; simp

theorem tauSum_inclF_zero (g : GGroup) (sp : GSpec) (hF : sp.kF ≤ g.cs.length) (y : ℝ) :
    tauSum (inclF g sp) 0 y = ∑ k ∈ range sp.kF, cK g k * Real.exp (-π * aR g * (y + sR g k) ^ 2) := by
  rw [tauSum_eq, inclF, List.map_map]
  have := sum_map_csR g (fun r => tauQ (quadF (aR g) r.1 r.2) 0 y) 0 sp.kF (by omega)
  rw [List.drop_zero] at this
  simp only [Function.comp_def]
  rw [this, zero_add, range_eq_Ico]
  refine sum_congr rfl (fun k _ => ?_)
  rw [tau_quadF]; simp

theorem tauSum_inclH_zero (g : GGroup) (sp : GSpec) (y : ℝ) :
    tauSum (inclH g sp) 0 y =
      if sp.hz then ∑ k ∈ range g.cs.length, cK g k * gbh (aR g) (sR g k) y else 0 := by
  unfold inclH
  split_ifs with hz
  · rw [tauSum_eq, List.map_map]
    simp only [Function.comp_def]
    rw [sum_map_csR_all g (fun r => tauQ (quadH (aR g) r.1 r.2) 0 y)]
    refine sum_congr rfl (fun k _ => ?_)
    rw [tau_quadH]
    simp [pw2R, gbh]
    ring
  · simp [tauSum]

/-! ## The geometric Gaussian tail -/

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) (by linarith)

/-- `Σ_{i<n} e^{-πa u_i²} ≤ 2 e^{-πaD²}` when `u_i ≥ D + iΔ`, `D > 0` and `2πaDΔ > 1`. -/
theorem gauss_geom_tail {a Δ D : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hD : 0 < D) (h1 : 1 < 2 * (π * a) * D * Δ) :
    ∀ (n : ℕ) (u : ℕ → ℝ), (∀ i < n, D + i * Δ ≤ u i) →
      ∑ i ∈ range n, Real.exp (-π * a * (u i) ^ 2) ≤ 2 * Real.exp (-π * a * D ^ 2) := by
  intro n u hu
  have hpa : 0 < π * a := by positivity
  have hterm : ∀ i < n, Real.exp (-π * a * (u i) ^ 2) ≤ Real.exp (-π * a * D ^ 2) * (1 / 2) ^ i := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h0 : 0 ≤ D + i * Δ := by positivity
    have hsq : (D + i * Δ) ^ 2 ≤ (u i) ^ 2 := pow_le_pow_left₀ h0 (hu i hi) 2
    have e1 : -π * a * (u i) ^ 2 ≤ -π * a * (D + i * Δ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq hpa.le; linarith
    have e2 : -π * a * (D + i * Δ) ^ 2 ≤ -π * a * D ^ 2 - i := by
      have h3 : (i : ℝ) ≤ (2 * (π * a) * D * Δ) * i := le_mul_of_one_le_left hi0 h1.le
      have h4 : 0 ≤ π * a * (i * Δ) ^ 2 := by positivity
      nlinarith
    calc Real.exp (-π * a * (u i) ^ 2) ≤ Real.exp (-π * a * D ^ 2 - i) := Real.exp_le_exp.mpr (e1.trans e2)
      _ = Real.exp (-π * a * D ^ 2) * Real.exp (-1) ^ i := by
          rw [sub_eq_add_neg, Real.exp_add, ← Real.exp_nat_mul]; congr 2; ring
      _ ≤ Real.exp (-π * a * D ^ 2) * (1 / 2) ^ i := by
          gcongr
          exact exp_neg_one_le_half
  calc ∑ i ∈ range n, Real.exp (-π * a * (u i) ^ 2) ≤ ∑ i ∈ range n, Real.exp (-π * a * D ^ 2) * (1 / 2) ^ i :=
        sum_le_sum (fun i hi => hterm i (mem_range.mp hi))
    _ = Real.exp (-π * a * D ^ 2) * ∑ i ∈ range n, (1 / 2 : ℝ) ^ i := by rw [mul_sum]
    _ ≤ Real.exp (-π * a * D ^ 2) * 2 := by gcongr; exact sum_geometric_two_le n
    _ = 2 * Real.exp (-π * a * D ^ 2) := by ring

/-! ## Coefficient bounds -/

theorem le_foldr_max : ∀ (L : List (Ball × Ball)) (b : Ball × Ball), b ∈ L →
    b.1.absHi ≤ L.foldr (fun cs acc => max cs.1.absHi acc) 0
  | [], b, hb => absurd hb List.not_mem_nil
  | x :: L, b, hb => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max L b hb') (le_max_right _ _)

theorem abs_cK_le {G : PG} (hG : PGOk P G) {k : ℕ} (hk : k < G.g.cs.length) :
    |cK G.g k| ≤ (cmaxHi G : ℝ) / 2 ^ P := by
  have hl := hG.hCS.length_eq
  have hk1 : k < G.g.csR.length := by rw [csR_length]; exact hk
  have hk2 : k < G.CS.length := by rw [← hl]; exact hk1
  have hm := (List.forall₂_iff_get.mp hG.hCS).2 k hk1 hk2
  simp only [List.get_eq_getElem] at hm
  rw [csR_getElem _ _ hk1] at hm
  have h1 := abs_le_absHi hm.1
  have h2 : ((G.CS[k]).1.absHi : ℝ) ≤ cmaxHi G := by
    exact_mod_cast le_foldr_max G.CS _ (List.getElem_mem hk2)
  calc |cK G.g k| ≤ ((G.CS[k]).1.absHi : ℝ) / 2 ^ P := h1
    _ ≤ (cmaxHi G : ℝ) / 2 ^ P := by gcongr

theorem sum_abs_le_foldr : ∀ {rs : List (ℝ × ℝ)} {bs : List (Ball × Ball)},
    List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2) rs bs →
      (rs.map fun r => |r.1|).sum ≤ ((bs.foldr (fun cs acc => cs.1.absHi + acc) 0 : ℕ) : ℝ) / 2 ^ P
  | [], [], _ => by simp
  | r :: rs, b :: bs, List.Forall₂.cons hr h => by
    simp only [List.map_cons, List.sum_cons, List.foldr_cons, Nat.cast_add, add_div]
    exact add_le_add (abs_le_absHi hr.1) (sum_abs_le_foldr h)

theorem sum_abs_cK_le {G : PG} (hG : PGOk P G) :
    ∑ k ∈ range G.g.cs.length, |cK G.g k| ≤ (csumHi G : ℝ) / 2 ^ P := by
  have := sum_abs_le_foldr hG.hCS
  rw [sum_map_csR_all G.g (fun r => |r.1|)] at this
  simp only at this
  exact this

/-- `|Σ_{k ∈ s} c_k f_k| ≤ (max |c|) Σ_{k ∈ s} f_k` for `f ≥ 0`, `s ⊆ [0, N)`. -/
theorem abs_sum_cK_le {G : PG} (hG : PGOk P G) (s : Finset ℕ) (hs : ∀ k ∈ s, k < G.g.cs.length)
    (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    |∑ k ∈ s, cK G.g k * f k| ≤ (cmaxHi G : ℝ) / 2 ^ P * ∑ k ∈ s, f k := by
  calc |∑ k ∈ s, cK G.g k * f k| ≤ ∑ k ∈ s, |cK G.g k * f k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, (cmaxHi G : ℝ) / 2 ^ P * f k := by
        refine sum_le_sum (fun k hk => ?_)
        rw [abs_mul, abs_of_nonneg (hf k)]
        exact mul_le_mul_of_nonneg_right (abs_cK_le hG (hs k hk)) (hf k)
    _ = (cmaxHi G : ℝ) / 2 ^ P * ∑ k ∈ s, f k := by rw [mul_sum]

/-! ## The tails -/

theorem gaussTail_sound {n : ℕ} {G : PG} (hG : PGOk P G) {Dr : ℝ} {D : Ball} (hD : mem P Dr D) {t : ℕ}
    (h : gaussTail P n G D = some t) :
    0 < Dr ∧ 1 < 2 * (π * aR G.g) * Dr * dR G.g ∧ 2 * Real.exp (-π * aR G.g * Dr ^ 2) ≤ (t : ℝ) / 2 ^ P := by
  unfold gaussTail at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hDpos := isPos_sound hD hc1
  have h2 := isPos_sound (mem_sub (mem_mul (mem_mul (mem_mulInt 2 hG.hpa) hD) hG.hD) (mem_ofInt P 1)) hc2
  push_cast at h2
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hmem := mem_expB' (mem_neg (mem_mul hG.hpa (mem_mul hD hD))) he
  have hle := abs_le_absHi hmem
  refine ⟨hDpos, by linarith, ?_⟩
  have e1 : Real.exp (-π * aR G.g * Dr ^ 2) = Real.exp (-(π * aR G.g * (Dr * Dr))) := by congr 1; ring
  rw [e1]
  have := le_abs_self (Real.exp (-(π * aR G.g * (Dr * Dr))))
  push_cast
  rw [mul_div_assoc]
  linarith

theorem dR_pos_of {G : PG} (hG : PGOk P G) {Dr : ℝ} (hD : 0 < Dr) (h1 : 1 < 2 * (π * aR G.g) * Dr * dR G.g) :
    0 < dR G.g := by
  by_contra hneg
  push_neg at hneg
  have : 2 * (π * aR G.g) * Dr * dR G.g ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by have := hG.hpos; positivity) hneg
  linarith

theorem mem_sk {G : PG} (hG : PGOk P G) (k : ℕ) : mem P (sR G.g k) (ofRat P (G.g.sk k).1 (G.g.sk k).2) := by
  have := mem_ofRat P (G.g.sk k).1 (G.g.sk k).2
    (by unfold GGroup.sk; have := hG.hs0d; have := hG.hdd; positivity)
  rwa [sk_eq _ hG.hs0d hG.hdd] at this

/-- E-terms below the window. -/
theorem low_tail {n : ℕ} {G : PG} (hG : PGOk P G) {k1 : ℕ} (hk1 : 0 < k1) {ylo : ℤ} {t : ℕ}
    (h : gaussTail P n G (sub ⟨ylo, 0⟩ (ofRat P (G.g.sk (k1 - 1)).1 (G.g.sk (k1 - 1)).2)) = some t)
    {y : ℝ} (hy : (ylo : ℝ) / 2 ^ P ≤ y) :
    ∑ k ∈ range k1, Real.exp (-π * aR G.g * (y - sR G.g k) ^ 2) ≤ (t : ℝ) / 2 ^ P := by
  have hD := mem_sub (mem_point' P ylo) (mem_sk hG (k1 - 1))
  obtain ⟨hDpos, h1, hb⟩ := gaussTail_sound hG hD h
  have hΔ := dR_pos_of hG hDpos h1
  rw [← sum_range_reflect]
  refine le_trans (gauss_geom_tail hG.hpos hΔ hDpos h1 k1 (fun i => y - sR G.g (k1 - 1 - i)) ?_) hb
  intro i hi
  have e := sR_succ G.g (k1 - 1 - i) i
  rw [show k1 - 1 - i + i = k1 - 1 by omega] at e
  linarith

/-- E-terms above the window. -/
theorem high_tail {n : ℕ} {G : PG} (hG : PGOk P G) {k2 : ℕ} {yhi : ℤ} {t : ℕ}
    (h : gaussTail P n G (sub (ofRat P (G.g.sk k2).1 (G.g.sk k2).2) ⟨yhi, 0⟩) = some t)
    {y : ℝ} (hy : y ≤ (yhi : ℝ) / 2 ^ P) (N : ℕ) :
    ∑ k ∈ Ico k2 N, Real.exp (-π * aR G.g * (y - sR G.g k) ^ 2) ≤ (t : ℝ) / 2 ^ P := by
  have hD := mem_sub (mem_sk hG k2) (mem_point' P yhi)
  obtain ⟨hDpos, h1, hb⟩ := gaussTail_sound hG hD h
  have hΔ := dR_pos_of hG hDpos h1
  rw [sum_Ico_eq_sum_range]
  have e2 : ∀ i, Real.exp (-π * aR G.g * (y - sR G.g (k2 + i)) ^ 2) =
      Real.exp (-π * aR G.g * (sR G.g (k2 + i) - y) ^ 2) := fun i => by congr 1; ring
  simp only [e2]
  refine le_trans (gauss_geom_tail hG.hpos hΔ hDpos h1 (N - k2) (fun i => sR G.g (k2 + i) - y) ?_) hb
  intro i _
  have e := sR_succ G.g k2 i
  linarith

/-- Mirror terms above the window. -/
theorem f_tail {n : ℕ} {G : PG} (hG : PGOk P G) {kF : ℕ} {ylo : ℤ} {t : ℕ}
    (h : gaussTail P n G (add ⟨ylo, 0⟩ (ofRat P (G.g.sk kF).1 (G.g.sk kF).2)) = some t)
    {y : ℝ} (hy : (ylo : ℝ) / 2 ^ P ≤ y) (N : ℕ) :
    ∑ k ∈ Ico kF N, Real.exp (-π * aR G.g * (y + sR G.g k) ^ 2) ≤ (t : ℝ) / 2 ^ P := by
  have hD := mem_add (mem_point' P ylo) (mem_sk hG kF)
  obtain ⟨hDpos, h1, hb⟩ := gaussTail_sound hG hD h
  have hΔ := dR_pos_of hG hDpos h1
  rw [sum_Ico_eq_sum_range]
  refine le_trans (gauss_geom_tail hG.hpos hΔ hDpos h1 (N - kF) (fun i => y + sR G.g (kF + i)) ?_) hb
  intro i _
  have e := sR_succ G.g kF i
  linarith

/-- The cosine terms, omitted. -/
theorem h_omit {n : ℕ} {G : PG} (hG : PGOk P G) {ylo : ℤ} (hylo : 0 ≤ ylo) {e : Ball}
    (he : expB' P n (neg (mul P (piB P) (mul P (mul P ⟨ylo, 0⟩ ⟨ylo, 0⟩) G.Ai))) = some e)
    {y : ℝ} (hy : (ylo : ℝ) / 2 ^ P ≤ y) :
    |∑ k ∈ range G.g.cs.length, cK G.g k * gbh (aR G.g) (sR G.g k) y| ≤
      ((cdiv ((mul P G.Q e).absHi * csumHi G) (2 ^ P) : ℕ) : ℝ) / 2 ^ P := by
  set a := aR G.g
  have ha := hG.hpos
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hyl0 : (0 : ℝ) ≤ (ylo : ℝ) / 2 ^ P := by
    apply div_nonneg _ hP.le; exact_mod_cast hylo
  have hQe : mem P (2 / Real.sqrt a * Real.exp (-π * ((ylo : ℝ) / 2 ^ P) ^ 2 / a)) (mul P G.Q e) := by
    have hm := mem_expB' (mem_neg (mem_mul (mem_piB P) (mem_mul (mem_mul (mem_point' P ylo) (mem_point' P ylo))
      hG.hAi))) he
    have e1 : -(π * ((ylo : ℝ) / 2 ^ P * ((ylo : ℝ) / 2 ^ P) * (1 / a))) = -π * ((ylo : ℝ) / 2 ^ P) ^ 2 / a := by ring
    rw [e1] at hm
    exact mem_mul hG.hQ hm
  set B := 2 / Real.sqrt a * Real.exp (-π * ((ylo : ℝ) / 2 ^ P) ^ 2 / a) with hB
  have hB0 : 0 ≤ B := by positivity
  have hBle := le_trans (le_abs_self B) (abs_le_absHi hQe)
  -- each term
  have hterm : ∀ k, |cK G.g k * gbh a (sR G.g k) y| ≤ |cK G.g k| * B := by
    intro k
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    unfold gbh
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a))]
    have hc := Real.abs_cos_le_one (2 * π * sR G.g k * y)
    have hexp : Real.exp (-π * y ^ 2 / a) ≤ Real.exp (-π * ((ylo : ℝ) / 2 ^ P) ^ 2 / a) := by
      apply Real.exp_le_exp.mpr
      have : ((ylo : ℝ) / 2 ^ P) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hyl0 hy 2
      have hpa : 0 < π / a := by positivity
      rw [show -π * y ^ 2 / a = -(π / a) * y ^ 2 by ring,
        show -π * ((ylo : ℝ) / 2 ^ P) ^ 2 / a = -(π / a) * ((ylo : ℝ) / 2 ^ P) ^ 2 by ring]
      nlinarith
    calc 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * |Real.cos (2 * π * sR G.g k * y)|
        ≤ 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * 1 := by gcongr
      _ ≤ B := by rw [mul_one, hB]; gcongr
  calc |∑ k ∈ range G.g.cs.length, cK G.g k * gbh a (sR G.g k) y|
      ≤ ∑ k ∈ range G.g.cs.length, |cK G.g k * gbh a (sR G.g k) y| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range G.g.cs.length, |cK G.g k| * B := sum_le_sum (fun k _ => hterm k)
    _ = (∑ k ∈ range G.g.cs.length, |cK G.g k|) * B := by rw [sum_mul]
    _ ≤ (csumHi G : ℝ) / 2 ^ P * ((mul P G.Q e).absHi : ℝ) / 2 ^ P := by
        rw [mul_div_assoc]
        exact mul_le_mul (sum_abs_cK_le hG) hBle hB0 (by positivity)
    _ ≤ ((cdiv ((mul P G.Q e).absHi * csumHi G) (2 ^ P) : ℕ) : ℝ) / 2 ^ P := by
        have hc := cdiv_spec ((mul P G.Q e).absHi * csumHi G) (2 ^ P) (by positivity)
        push_cast at hc
        have : (csumHi G : ℝ) / 2 ^ P * ((mul P G.Q e).absHi : ℝ) / 2 ^ P =
            (((mul P G.Q e).absHi : ℝ) * (csumHi G : ℝ) / 2 ^ P) / 2 ^ P := by ring
        rw [this]
        gcongr

/-! ## The omitted terms of a group -/

theorem omitG_sound {n : ℕ} {G : PG} (hG : PGOk P G) {sp : GSpec} {ylo yhi : ℤ} {R : ℕ}
    (h : omitG P n G sp ylo yhi = some R) {y : ℝ} (hy1 : (ylo : ℝ) / 2 ^ P ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ P) :
    |gsum G.g.triples y - tauSum (incl G.g sp) 0 y| ≤ (R : ℝ) / 2 ^ P := by
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
  -- the tails
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
  have hD : (if sp.hz then (0 : ℝ) else ∑ k ∈ range N, cK g k * gbh a (sR g k) y) ≤
      |if sp.hz then (0 : ℝ) else ∑ k ∈ range N, cK g k * gbh a (sR g k) y| := le_abs_self _
  have hD' : |if sp.hz then (0 : ℝ) else ∑ k ∈ range N, cK g k * gbh a (sR g k) y| ≤ (td : ℝ) / 2 ^ P := by
    split_ifs at htd with hz
    · simp only [Option.some.injEq] at htd; subst htd; simp [hz]
    · simp only [Option.map_eq_some_iff] at htd
      obtain ⟨e, he, rfl⟩ := htd
      simp only [hz, if_false]
      exact h_omit hG hylo he hy1
  -- the decomposition
  have hsplit : gsum g.triples y - tauSum (incl g sp) 0 y =
      ∑ k ∈ range sp.k1, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
      ∑ k ∈ Ico sp.k2 N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
      ∑ k ∈ Ico sp.kF N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) +
      (if sp.hz then (0 : ℝ) else ∑ k ∈ range N, cK g k * gbh a (sR g k) y) := by
    rw [gsum_triples, incl, tauSum_append, tauSum_append, tauSum_inclE_zero g sp h12 h2N,
      tauSum_inclF_zero g sp hFN, tauSum_inclH_zero]
    have eE : ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) =
        ∑ k ∈ range sp.k1, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
        ∑ k ∈ Ico sp.k1 sp.k2, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
        ∑ k ∈ Ico sp.k2 N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) := by
      rw [sum_range_add_sum_Ico _ h12, sum_range_add_sum_Ico _ h2N]
    have eF : ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) =
        ∑ k ∈ range sp.kF, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) +
        ∑ k ∈ Ico sp.kF N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) := by
      rw [sum_range_add_sum_Ico _ hFN]
    have eT : ∑ k ∈ range N, cK g k * (gb a (sR g k) y + gbh a (sR g k) y) =
        ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y - sR g k) ^ 2) +
        ∑ k ∈ range N, cK g k * Real.exp (-π * a * (y + sR g k) ^ 2) +
        ∑ k ∈ range N, cK g k * gbh a (sR g k) y := by
      rw [← sum_add_distrib, ← sum_add_distrib]
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
  have t1 := abs_add_le (A + B + C) D
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

end SignUnc.Chk
