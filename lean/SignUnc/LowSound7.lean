import SignUnc.LowSound6

/-!
# Soundness of the lower checker, part 7: the tail `y ≥ Y` (`ltailOK`)

`|Σ c (b - b̂)| ≤ Σ_k |c_k| (2 e^{-πa(Y - s_max)²} + (2/√a) e^{-πY²/a})` for `y ≥ Y ≥ s_max` (centres `s_k ≥ 0`),
`Σ d cos ≤ Σ d` (`d ≥ 0`), `|P̂| ≤ 2 (jumps)`: `1 - v + P̂ > m + 2rε` on `[Y, ∞)`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Finset

variable {P : ℕ}

/-! ## The Gaussian part of `v` -/

theorem sR_nonneg (g : GGroup) (hs : 0 ≤ g.s0n) (k : ℕ) : 0 ≤ sR g k := by
  unfold sR
  have h1 : (0 : ℝ) ≤ (g.s0n : ℝ) := by exact_mod_cast hs
  positivity

theorem sR_mono (g : GGroup) {k k' : ℕ} (h : k ≤ k') : sR g k ≤ sR g k' := by
  unfold sR
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (g.dn : ℝ) / g.dd := by positivity
  nlinarith

theorem abs_gb_le {a s y Δ : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ) (hy : Δ ≤ y - s) :
    |gb a s y| ≤ 2 * Real.exp (-(π * a * (Δ * Δ))) := by
  unfold gb
  have h1 : Real.exp (-π * a * (y - s) ^ 2) ≤ Real.exp (-(π * a * (Δ * Δ))) := by
    apply Real.exp_le_exp.mpr
    have : Δ * Δ ≤ (y - s) ^ 2 := by nlinarith
    have hpa : 0 < π * a := by positivity
    nlinarith
  have h2 : Real.exp (-π * a * (y + s) ^ 2) ≤ Real.exp (-(π * a * (Δ * Δ))) := by
    apply Real.exp_le_exp.mpr
    have : Δ * Δ ≤ (y + s) ^ 2 := by nlinarith
    have hpa : 0 < π * a := by positivity
    nlinarith
  rw [abs_of_nonneg (by positivity)]
  linarith

theorem abs_gbh_le {a s y Y : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) (hy : Y ≤ y) :
    |gbh a s y| ≤ 2 / Real.sqrt a * Real.exp (-(π * (Y * Y * (1 / a)))) := by
  unfold gbh
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.sqrt a),
    abs_of_nonneg (Real.exp_pos _).le]
  have h1 : Real.exp (-π * y ^ 2 / a) ≤ Real.exp (-(π * (Y * Y * (1 / a)))) := by
    apply Real.exp_le_exp.mpr
    have hYy : Y * Y ≤ y ^ 2 := by nlinarith
    rw [show -π * y ^ 2 / a = -(π * (y ^ 2 * (1 / a))) by ring]
    have : π * (Y * Y * (1 / a)) ≤ π * (y ^ 2 * (1 / a)) := by
      apply mul_le_mul_of_nonneg_left _ pi_pos.le
      exact mul_le_mul_of_nonneg_right hYy (by positivity)
    linarith
  have h2 := Real.abs_cos_le_one (2 * π * s * y)
  have h3 : 0 ≤ 2 / Real.sqrt a := by positivity
  calc 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * |Real.cos (2 * π * s * y)|
      ≤ 2 / Real.sqrt a * Real.exp (-(π * (Y * Y * (1 / a)))) * 1 := by
        gcongr
    _ = _ := by ring

theorem vGtail_sound {n YT : ℕ} {y : ℝ} (hy : (YT : ℝ) ≤ y) :
    ∀ {gs : List GGroup} {pgs : List PG4} {V : ℕ},
      List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs →
      (∀ g ∈ gs, 0 ≤ g.s0n) →
      vGtail P n YT pgs = some V →
      |vsum (gs.flatMap GGroup.triples) y| ≤ (V : ℝ) / 2 ^ P
  | [], [], V, List.Forall₂.nil, _, h => by
    simp only [vGtail, Option.some.injEq] at h
    subst h
    simp [vsum]
  | _ :: gs, G :: pgs, V, List.Forall₂.cons hG hgs, hs, h => by
    obtain ⟨hGok, rfl⟩ := hG
    have hP : (0 : ℝ) < 2 ^ P := by positivity
    have hGG := hGok.hG
    have hs0 : 0 ≤ G.G.g.s0n := hs _ (by simp)
    unfold vGtail at h
    dsimp only at h
    split_ifs at h with hD
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨e1, he1, e2, he2, rest, hrest, rfl⟩ := h
    have ih := vGtail_sound hy hgs (fun g' hg' => hs g' (by simp [hg'])) hrest
    rw [List.flatMap_cons, vsum_append]
    -- the data of the group
    set N := G.G.g.cs.length with hN
    have hapos : 0 < aR G.G.g := hGG.hpos
    set smax := sR G.G.g (N - 1) with hsmax
    have hYb : mem P (YT : ℝ) (ofInt P (YT : ℤ)) := by simpa using mem_ofInt P (YT : ℤ)
    have hsm : mem P smax (ofRat P (G.G.g.sk (N - 1)).1 (G.G.g.sk (N - 1)).2) := by
      rw [hsmax, ← sk_eq G.G.g hGG.hs0d hGG.hdd]
      exact mem_ofRat P _ _ (by unfold GGroup.sk; exact Nat.mul_pos hGG.hs0d hGG.hdd)
    have hDm := mem_sub hYb hsm
    have hDpos : 0 < (YT : ℝ) - smax := by
      have h1 := (abs_le.mp hDm).1
      unfold isPos at hD
      have hr := decide_eq_true_iff.mp hD
      have hr' : ((sub (ofInt P (YT : ℤ)) (ofRat P (G.G.g.sk (N - 1)).1 (G.G.g.sk (N - 1)).2)).r : ℝ) <
          ((sub (ofInt P (YT : ℤ)) (ofRat P (G.G.g.sk (N - 1)).1 (G.G.g.sk (N - 1)).2)).m : ℝ) := by
        exact_mod_cast hr
      have h3 : (0 : ℝ) < ((sub (ofInt P (YT : ℤ)) (ofRat P (G.G.g.sk (N - 1)).1 (G.G.g.sk (N - 1)).2)).m : ℝ) /
          2 ^ P - ((sub (ofInt P (YT : ℤ)) (ofRat P (G.G.g.sk (N - 1)).1 (G.G.g.sk (N - 1)).2)).r : ℝ) / 2 ^ P := by
        rw [← sub_div]; exact div_pos (by linarith) hP
      linarith
    have he1m := mem_expB' (mem_neg (mem_mul hGG.hpa (mem_mul hDm hDm))) he1
    have he2m := mem_expB' (mem_neg (mem_mul (mem_piB P) (mem_mul (mem_mul hYb hYb) hGG.hAi))) he2
    have hsum := mem_add (mem_mulInt 2 he1m) (mem_mul hGG.hQ he2m)
    set B : ℝ := ((2 : ℤ) : ℝ) * Real.exp (-(π * aR G.G.g * (((YT : ℝ) - smax) * ((YT : ℝ) - smax)))) +
      2 / Real.sqrt (aR G.G.g) * Real.exp (-(π * ((YT : ℝ) * (YT : ℝ) * (1 / aR G.G.g)))) with hB
    have hBle : B ≤ ((add (mulInt 2 e1) (mul P G.G.Q e2)).absHi : ℝ) / 2 ^ P :=
      (le_abs_self _).trans (abs_le_absHi hsum)
    -- the group bound
    have hgroup : |vsum G.G.g.triples y| ≤ (csumHi G.G : ℝ) / 2 ^ P * B := by
      rw [vsum_triples]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hk : ∀ k ∈ range N, |cK G.G.g k * (gb (aR G.G.g) (sR G.G.g k) y - gbh (aR G.G.g) (sR G.G.g k) y)| ≤
          |cK G.G.g k| * B := by
        intro k hk
        rw [mem_range] at hk
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hsk0 := sR_nonneg G.G.g hs0 k
        have hsk1 : sR G.G.g k ≤ smax := sR_mono G.G.g (by omega)
        have h1 := abs_gb_le hapos hsk0 hDpos.le (show (YT : ℝ) - smax ≤ y - sR G.G.g k by linarith)
        have h2 := abs_gbh_le (s := sR G.G.g k) hapos (by positivity : (0 : ℝ) ≤ YT) hy
        calc |gb (aR G.G.g) (sR G.G.g k) y - gbh (aR G.G.g) (sR G.G.g k) y|
            ≤ |gb (aR G.G.g) (sR G.G.g k) y| + |gbh (aR G.G.g) (sR G.G.g k) y| := abs_sub _ _
          _ ≤ B := by rw [hB]; push_cast; linarith
      refine (sum_le_sum hk).trans ?_
      rw [← sum_mul]
      have hB0 : 0 ≤ B := by rw [hB]; push_cast; positivity
      exact mul_le_mul_of_nonneg_right (sum_abs_cK_le hGG) hB0
    have hcd := cdiv_spec ((add (mulInt 2 e1) (mul P G.G.Q e2)).absHi * csumHi G.G) (2 ^ P) (by positivity)
    have hcs0 : (0 : ℝ) ≤ (csumHi G.G : ℝ) / 2 ^ P := by positivity
    have hstep : (csumHi G.G : ℝ) / 2 ^ P * B ≤
        ((cdiv ((add (mulInt 2 e1) (mul P G.G.Q e2)).absHi * csumHi G.G) (2 ^ P) : ℕ) : ℝ) / 2 ^ P := by
      calc (csumHi G.G : ℝ) / 2 ^ P * B ≤ (csumHi G.G : ℝ) / 2 ^ P *
            (((add (mulInt 2 e1) (mul P G.G.Q e2)).absHi : ℝ) / 2 ^ P) := mul_le_mul_of_nonneg_left hBle hcs0
        _ = (((add (mulInt 2 e1) (mul P G.G.Q e2)).absHi * csumHi G.G : ℕ) : ℝ) / ((2 ^ P : ℕ) : ℝ) / 2 ^ P := by
            push_cast; ring
        _ ≤ _ := by gcongr
    calc |vsum G.G.g.triples y + vsum (gs.flatMap GGroup.triples) y|
        ≤ |vsum G.G.g.triples y| + |vsum (gs.flatMap GGroup.triples) y| := abs_add_le _ _
      _ ≤ ((cdiv ((add (mulInt 2 e1) (mul P G.G.Q e2)).absHi * csumHi G.G) (2 ^ P) : ℕ) : ℝ) / 2 ^ P +
          (rest : ℝ) / 2 ^ P := add_le_add (hgroup.trans hstep) ih
      _ = _ := by push_cast; ring
  | [], _ :: _, V, h, _, _ => by cases h
  | _ :: _, [], V, h, _, _ => by cases h

/-! ## The cosines -/

theorem mem_dsum : ∀ (cos : List (ℕ × ℕ × ℤ × ℕ)), (∀ q ∈ cos, 0 < q.2.2.2) →
    mem P ((cos.map fun q => (q.2.2.1 : ℝ) / q.2.2.2).sum) ((cos.map fun q => ofRat P q.2.2.1 q.2.2.2).foldr add ⟨0, 0⟩)
  | [], _ => by simpa using mem_zero_ball (P := P)
  | q :: L, h => by
    simp only [List.map_cons, List.sum_cons, List.foldr_cons]
    exact mem_add (mem_ofRat P _ _ (h q (by simp))) (mem_dsum L (fun q' hq' => h q' (by simp [hq'])))

theorem tauSum_cosTerms_zero (cos : List (ℕ × ℕ × ℤ × ℕ)) (y : ℝ) :
    tauSum (cosTerms cos) 0 y = (cos.map fun q => (q.2.2.1 : ℝ) / q.2.2.2 * Real.cos (2 * π * ((q.1 : ℝ) / q.2.1) * y)).sum := by
  rw [tauSum_eq, cosTerms, List.map_map]
  congr 1
  refine List.map_congr_left (fun q _ => ?_)
  simp only [Function.comp_apply]
  rw [tau_quadC]
  simp [pw2R]

theorem cos_sum_le (cos : List (ℕ × ℕ × ℤ × ℕ)) (hd : ∀ q ∈ cos, 0 ≤ q.2.2.1) (y : ℝ) :
    (cos.map fun q => (q.2.2.1 : ℝ) / q.2.2.2 * Real.cos (2 * π * ((q.1 : ℝ) / q.2.1) * y)).sum ≤
      (cos.map fun q => (q.2.2.1 : ℝ) / q.2.2.2).sum := by
  refine listSum_le_listSum cos (fun q hq => ?_)
  have h0 : (0 : ℝ) ≤ (q.2.2.1 : ℝ) / q.2.2.2 := by
    have : (0 : ℝ) ≤ (q.2.2.1 : ℝ) := by exact_mod_cast hd q hq
    positivity
  calc (q.2.2.1 : ℝ) / q.2.2.2 * Real.cos (2 * π * ((q.1 : ℝ) / q.2.1) * y) ≤ (q.2.2.1 : ℝ) / q.2.2.2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) h0
    _ = _ := mul_one _

/-! ## The tail -/

theorem ltailOK_sound (c : LCfg) (gs : List GGroup) (cos : List (ℕ × ℕ × ℤ × ℕ)) (ps : List PPiece)
    (h : ltailOK c gs cos ps = true) (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2) (hs0 : ∀ g ∈ gs, 0 ≤ g.s0n)
    (hch : chainOK 0 ps = true) (hord : ∀ pc ∈ ps, pc.1 < pc.2.1) (hlen : ∀ pc ∈ ps, pc.2.2.length = c.D + 1)
    (hYT : 0 < c.YT) :
    ∀ y, (c.YT : ℝ) ≤ y →
      ((c.m + (mul c.P (mulInt 2 (ofRat c.P 2751 5000)) ⟨(c.eps : ℤ), 0⟩).absHi : ℕ) : ℝ) / 2 ^ c.P <
        1 - (vsum (gs.flatMap GGroup.triples) y + tauSum (cosTerms cos) 0 y) + PhatS c.P ps y := by
  intro y hy
  unfold ltailOK at h
  split at h
  · rename_i pgs hpgs hall
    split at h
    · rename_i vg hvg
      simp only [decide_eq_true_eq] at h
      have hP : (0 : ℝ) < 2 ^ c.P := by positivity
      have hF := prepGroupsV_ok hpgs
      have hv := vGtail_sound hy hF hs0 hvg
      have hd : ∀ q ∈ cos, 0 ≤ q.2.2.1 := by
        intro q hq
        have := List.all_eq_true.mp hall q hq
        simpa using this
      have hcosv := (tauSum_cosTerms_zero cos y).trans_le (cos_sum_le cos hd y)
      have hds := (le_abs_self _).trans (abs_le_absHi (mem_dsum (P := c.P) cos (fun q hq => (hcos q hq).2)))
      have hph := phat_tail (P := c.P) (D := c.D) hYT hch hord hlen hy
      have hR := (Nat.cast_lt (α := ℝ)).mpr h
      have hR' := div_lt_div_of_pos_right hR hP
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_div] at hR'
      rw [Nat.cast_pow, Nat.cast_ofNat, div_self hP.ne'] at hR'
      simp only [mul_div_assoc, add_div] at hR'
      push_cast at hph ⊢
      rw [add_div] at hph ⊢
      have h1 := (abs_le.mp hv).2
      have h2 := (abs_le.mp hph).1
      linarith
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end SignUnc.Chk
