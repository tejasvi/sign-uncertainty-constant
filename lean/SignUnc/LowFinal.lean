import SignUnc.LowSound7
import SignUnc.Lower.Criterion
import SignUnc.Lower.Strict
import SignUnc.Lower.Fejer
import SignUnc.Lower.Kappa
import SUCert.LowCfg

/-!
# The lower bound from the checker

`lower_weak_of`: if the base check (`lbaseOK`: the approximant `P`, `|ρ| ≤ δ`, the tail and the cover of `[r, Y]`
by the segments) and every segment check pass, then `A₊(1)² ≥ 0.5502²` and `C_{6.11} ≥ 0.5502²`
(`LowerStatementWeak`).  With `ExtremizerHyp` the bounds are strict, and with the upper half this is
`MainStatement`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Finset MeasureTheory SignUnc.LowData

variable {P : ℕ}

/-! ## The pieces of `P` -/

theorem pieceP_OK_facts {n k D L : ℕ} {pgs : List PG4} {sps : List GSpec} {cos : List (ℕ × ℕ × ℤ × ℕ)}
    {psi : List Ball} {eps R : ℕ} {pc : PPiece} (h : pieceP_OK P n k D L pgs sps cos psi eps R pc = true) :
    pc.1 < pc.2.1 ∧ pc.2.2.length = D + 1 := by
  unfold pieceP_OK at h
  dsimp only at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, h.1.2⟩
  · simp at h

theorem pieceP_OK'_sound {n k D L : ℕ} {gs : List GGroup} {pgs : List PG4}
    (hgs : List.Forall₂ (fun (g : GGroup) (G : PG4) => PGVOk P G ∧ G.G.g = g) gs pgs)
    {cos : List (ℕ × ℕ × ℤ × ℕ)} (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2)
    {psi : List (ℤ × ℕ)} (hpsi : ∀ q ∈ psi, 0 < q.2) {eps : ℕ} {x : PPiece × List GSpec}
    (h : pieceP_OK' P n k D L pgs cos (psiPoly P psi) eps x = true) :
    x.1.1 < x.1.2.1 ∧ x.1.2.2.length = D + 1 ∧
    ∀ t ∈ Set.Icc (plo x.1) (phi' x.1),
      |1 - (vsum (gs.flatMap GGroup.triples) t + tauSum (cosTerms cos) 0 t) + Tpoly (psiR psi) 0 t - Peval P x.1 t| ≤
        (eps : ℝ) / 2 ^ P := by
  obtain ⟨pc, sps⟩ := x
  unfold pieceP_OK' at h
  split at h
  · rename_i R hR
    obtain ⟨hlt, hlen⟩ := pieceP_OK_facts h
    refine ⟨hlt, hlen, fun t ht => ?_⟩
    have hP : (0 : ℝ) < 2 ^ P := by positivity
    have ht1 : ((pc.1 : ℕ) : ℝ) / 10000 ≤ t := ht.1
    have ht2 : t ≤ ((pc.2.1 : ℕ) : ℝ) / 10000 := ht.2
    have hy1 : ((((pc.1 * 2 ^ P / 10000 : ℕ) : ℤ)) : ℝ) / 2 ^ P ≤ t := by
      rw [Int.cast_natCast]
      have h1 : ((pc.1 * 2 ^ P / 10000 : ℕ) : ℝ) ≤ ((pc.1 * 2 ^ P : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) := Nat.cast_div_le
      have h2 : ((pc.1 * 2 ^ P / 10000 : ℕ) : ℝ) / 2 ^ P ≤ ((pc.1 : ℕ) : ℝ) / 10000 := by
        rw [div_le_iff₀ hP]
        calc ((pc.1 * 2 ^ P / 10000 : ℕ) : ℝ) ≤ ((pc.1 * 2 ^ P : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) := h1
          _ = ((pc.1 : ℕ) : ℝ) / 10000 * 2 ^ P := by push_cast; ring
      linarith
    have hy2 : t ≤ (((((pc.2.1 * 2 ^ P + 9999) / 10000 : ℕ) : ℤ)) : ℝ) / 2 ^ P := by
      rw [Int.cast_natCast]
      have hn : pc.2.1 * 2 ^ P ≤ 10000 * ((pc.2.1 * 2 ^ P + 9999) / 10000) := by omega
      have hn' : ((pc.2.1 * 2 ^ P : ℕ) : ℝ) ≤ 10000 * (((pc.2.1 * 2 ^ P + 9999) / 10000 : ℕ) : ℝ) := by
        exact_mod_cast hn
      have h2 : ((pc.2.1 : ℕ) : ℝ) / 10000 ≤ (((pc.2.1 * 2 ^ P + 9999) / 10000 : ℕ) : ℝ) / 2 ^ P := by
        rw [le_div_iff₀ hP]
        push_cast at hn'
        linarith
      linarith
    have hom := omitAllV_sound hy1 hy2 hgs hR
    have hp := pieceP_OK_sound hgs hcos hpsi h ht1 ht2
    have hT : Tphi gs sps cos psi 0 t =
        1 + Tpoly (psiR psi) 0 t - (tauSum (inclAllV gs sps) 0 t + tauSum (cosTerms cos) 0 t) := by
      unfold Tphi vTerms
      rw [tauSum_append]
      simp
    rw [hT] at hp
    have e : 1 - (vsum (gs.flatMap GGroup.triples) t + tauSum (cosTerms cos) 0 t) + Tpoly (psiR psi) 0 t -
        Peval P pc t = (1 + Tpoly (psiR psi) 0 t - (tauSum (inclAllV gs sps) 0 t + tauSum (cosTerms cos) 0 t) -
          Peval P pc t) - (vsum (gs.flatMap GGroup.triples) t - tauSum (inclAllV gs sps) 0 t) := by ring
    rw [e]
    calc _ ≤ |1 + Tpoly (psiR psi) 0 t - (tauSum (inclAllV gs sps) 0 t + tauSum (cosTerms cos) 0 t) - Peval P pc t| +
          |vsum (gs.flatMap GGroup.triples) t - tauSum (inclAllV gs sps) 0 t| := abs_sub _ _
      _ ≤ _ := by linarith
  · simp at h

theorem mem_zip_of_mem {α β : Type*} {l₁ : List α} {l₂ : List β} (hl : l₁.length = l₂.length) {a : α}
    (ha : a ∈ l₁) : ∃ b, (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  refine ⟨l₂[i]'(by rw [← hl]; exact hi), ?_⟩
  have h : i < (l₁.zip l₂).length := by rw [List.length_zip, ← hl, min_self]; exact hi
  have := List.getElem_mem h
  rw [List.getElem_zip] at this
  exact this

theorem pOK_sound {n k D L : ℕ} {gs : List GGroup} {cos : List (ℕ × ℕ × ℤ × ℕ)} {psi : List (ℤ × ℕ)} {eps : ℕ}
    {ps : List PPiece} {pss : List (List GSpec)} (h : pOK P n k D L gs cos psi eps ps pss = true)
    (hcos : ∀ q ∈ cos, 0 < q.2.1 ∧ 0 < q.2.2.2) (hpsi : ∀ q ∈ psi, 0 < q.2) :
    chainOK 0 ps = true ∧
    (∀ pc ∈ ps, pc.1 < pc.2.1 ∧ pc.2.2.length = D + 1 ∧
      ∀ t ∈ Set.Icc (plo pc) (phi' pc), |1 - (vsum (gs.flatMap GGroup.triples) t + tauSum (cosTerms cos) 0 t) +
        Tpoly (psiR psi) 0 t - Peval P pc t| ≤ (eps : ℝ) / 2 ^ P) ∧
    ∃ pgs, prepGroupsV P n gs = some pgs := by
  unfold pOK at h
  split at h
  · rename_i pgs hpgs
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨hch, hlen⟩, hall⟩ := h
    have hF := prepGroupsV_ok hpgs
    refine ⟨hch, fun pc hpc => ?_, pgs, hpgs⟩
    obtain ⟨sps, hmem⟩ := mem_zip_of_mem hlen hpc
    exact pieceP_OK'_sound hF hcos hpsi (hall _ hmem)
  · simp at h

/-! ## The segments cover `[⌊r 2^P⌋, Y]` -/

theorem lcontigEnd_cover : ∀ (segs : List LSeg) (lo e : ℤ), lcontigEnd lo segs = some e →
    ∀ y : ℝ, (lo : ℝ) / 2 ^ P ≤ y → y < (e : ℝ) / 2 ^ P →
      ∃ s ∈ segs, (s.lo : ℝ) / 2 ^ P ≤ y ∧ y ≤ (runsEnd s.lo s.ws : ℝ) / 2 ^ P ∧ s.ws ≠ [] ∧ ∀ r ∈ s.ws, 0 < r.2
  | [], lo, e, h, y, h1, h2 => by
    simp only [lcontigEnd, Option.some.injEq] at h
    subst h
    exact absurd h2 (not_lt.mpr h1)
  | s :: ss, lo, e, h, y, h1, h2 => by
    unfold lcontigEnd at h
    split_ifs at h with hs
    obtain ⟨hlo, hne, hpos⟩ := hs
    have hpos' : ∀ r ∈ s.ws, 0 < r.2 := by
      intro r hr
      have := List.all_eq_true.mp hpos r hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    rcases le_or_gt y ((runsEnd s.lo s.ws : ℝ) / 2 ^ P) with hle | hgt
    · exact ⟨s, by simp, by rw [hlo]; exact h1, hle, hne, hpos'⟩
    · obtain ⟨s', hs', h3⟩ := lcontigEnd_cover ss _ e h y hgt.le h2
      exact ⟨s', by simp [hs'], h3⟩

/-! ## The certificate -/

end SignUnc.Chk

namespace SignUnc

open SignUnc.Chk SignUnc.LowData Real Ival Ival.Ball

/-- The certificate of the lower bound (`r = 0.5502`). -/
noncomputable def lowCert : LCert where
  r := 2751 / 5000
  pairs := lowGroups.flatMap GGroup.triples
  coss := lowCos.map fun q => ((q.1 : ℝ) / q.2.1, (q.2.2.1 : ℝ) / q.2.2.2)
  psi := fun x => Tpoly (psiR lowPsi) 0 x

theorem continuous_Tpoly0 : ∀ a : List ℝ, Continuous (fun y => Tpoly a 0 y)
  | [] => by
    show Continuous fun _ => (0 : ℝ)
    exact continuous_const
  | c :: cs => by
    have := continuous_Tpoly0 cs
    show Continuous fun y => c + y * Tpoly cs 0 y
    fun_prop

theorem lowCos_pos : ∀ q ∈ lowCos, 0 < q.2.1 ∧ 0 < q.2.2.2 := by decide +kernel

theorem lowPsi_pos : ∀ q ∈ lowPsi, 0 < q.2 := by decide +kernel

theorem lowGroups_s0 : ∀ g ∈ lowGroups, 0 ≤ g.s0n := by decide +kernel

theorem lowGroups_a : ∀ g ∈ lowGroups, 0 < g.an ∧ 0 < g.ad := by decide +kernel

theorem lowGroups_apos : ∀ p ∈ lowGroups.flatMap GGroup.triples, 0 < p.1 := by
  intro p hp
  rw [List.mem_flatMap] at hp
  obtain ⟨g, hg, hpg⟩ := hp
  unfold GGroup.triples at hpg
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hpg
  obtain ⟨h1, h2⟩ := lowGroups_a g hg
  show 0 < aR g
  unfold aR
  have : (0 : ℝ) < g.an := by exact_mod_cast h1
  have : (0 : ℝ) < g.ad := by exact_mod_cast h2
  positivity

theorem lowCert_pairs : lowCert.pairs = lowGroups.flatMap GGroup.triples := by
  simp only [lowCert]

theorem lowCert_vG (y : ℝ) : lowCert.vG y = vsum (lowGroups.flatMap GGroup.triples) y := by
  unfold LCert.vG vsum
  rw [lowCert_pairs]

theorem lowCert_vC (y : ℝ) : lowCert.vC y = tauSum (cosTerms lowCos) 0 y := by
  rw [tauSum_cosTerms_zero]
  unfold LCert.vC
  simp only [lowCert, List.map_map, Function.comp_def]

theorem lowCert_v (y : ℝ) :
    lowCert.v y = vsum (lowGroups.flatMap GGroup.triples) y + tauSum (cosTerms lowCos) 0 y := by
  unfold LCert.v
  rw [lowCert_vG, lowCert_vC]

theorem lowCert_r : lowCert.r = 2751 / 5000 := rfl

theorem lowCert_hβ : ∀ q ∈ lowCert.coss, lowCert.r ≤ q.1 ∧ 0 ≤ q.2 := by
  intro q hq
  rw [lowCert_r]
  simp only [lowCert, lowCos, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem lowCert_hψe : ∀ x, lowCert.psi (-x) = lowCert.psi x := by
  intro x
  show Tpoly (psiR lowPsi) 0 (-x) = Tpoly (psiR lowPsi) 0 x
  rw [Tpoly_psiR lowPsi lowPsi.length le_rfl, Tpoly_psiR lowPsi lowPsi.length le_rfl]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [pow_mul, pow_mul, neg_sq]

theorem lowCert_ok : lowCert.Ok where
  hr := by rw [lowCert_r]; norm_num
  ha := by rw [lowCert_pairs]; exact lowGroups_apos
  hβ := lowCert_hβ
  hψc := continuous_Tpoly0 (psiR lowPsi)
  hψe := lowCert_hψe

/-! ## The lower bound -/

theorem lower_Sr_of (segs : List LSeg)
    (hbase : lbaseOK lowCfg lowGroups lowCos lowPsi lowP lowPSS segs = true)
    (hsegs : ∀ s ∈ segs, lsegOK lowCfg lowGroups lowCos lowP s = true) : Sr (2751 / 5000) := by
  unfold lbaseOK at hbase
  simp only [Bool.and_eq_true] at hbase
  obtain ⟨⟨⟨hp, hr⟩, ht⟩, hm⟩ := hbase
  obtain ⟨hch, hpcs, -⟩ := pOK_sound hp lowCos_pos lowPsi_pos
  have hord : ∀ pc ∈ lowP, pc.1 < pc.2.1 := fun pc hpc => (hpcs pc hpc).1
  have hlen : ∀ pc ∈ lowP, pc.2.2.length = lowCfg.D + 1 := fun pc hpc => (hpcs pc hpc).2.1
  rcases he : lcontigEnd ((2751 * 2 ^ lowCfg.P / 5000 : ℕ) : ℤ) segs with _ | e
  · rw [he] at hm; simp at hm
  rw [he] at hm
  simp only [decide_eq_true_eq] at hm
  have hOk := lowCert_ok
  have hP : (0 : ℝ) < 2 ^ lowCfg.P := by positivity
  set ε : ℝ := (lowCfg.eps : ℝ) / 2 ^ lowCfg.P with hεdef
  -- `|φ₀ - P_k| ≤ ε` on the pieces, hence `|φ̂ - P̂| ≤ 2rε`
  have hε : ∀ pc ∈ lowP, ∀ t ∈ Set.Icc (plo pc) (phi' pc),
      |1 - lowCert.v t + lowCert.psi t - Peval lowCfg.P pc t| ≤ ε := by
    intro pc hpc t ht
    rw [lowCert_v]
    exact (hpcs pc hpc).2.2 t ht
  have hφ := fun y => phihat_PhatS hOk (by norm_num [lowCert]) hch (fun pc hpc => (hord pc hpc).le) hε y
  have h2e : 2 * lowCert.r * ε ≤
      ((mul lowCfg.P (mulInt 2 (ofRat lowCfg.P 2751 5000)) ⟨(lowCfg.eps : ℤ), 0⟩).absHi : ℝ) / 2 ^ lowCfg.P := by
    have := abs_le_absHi (mem_mul (mem_mulInt 2 (mem_r lowCfg.P)) (mem_point lowCfg.P (lowCfg.eps : ℤ)))
    refine le_trans (le_of_eq ?_) ((le_abs_self _).trans this)
    rw [hεdef]
    simp only [lowCert]
    push_cast
    ring
  -- `W ≥ m` on `(r, ∞)`
  have hW : ∀ y, lowCert.r < y → (lowCfg.m : ℝ) / 2 ^ lowCfg.P ≤ lowCert.W y := by
    intro y hy
    have hy' : (2751 / 5000 : ℝ) < y := hy
    have hbound : ((lowCfg.m + (mul lowCfg.P (mulInt 2 (ofRat lowCfg.P 2751 5000)) ⟨(lowCfg.eps : ℤ), 0⟩).absHi : ℕ) :
        ℝ) / 2 ^ lowCfg.P <
        1 - (vsum (lowGroups.flatMap GGroup.triples) y + tauSum (cosTerms lowCos) 0 y) + PhatS lowCfg.P lowP y := by
      rcases le_or_gt (lowCfg.YT : ℝ) y with hYy | hYy
      · exact ltailOK_sound lowCfg lowGroups lowCos lowP ht lowCos_pos lowGroups_s0 hch hord hlen
          (by decide +kernel) y hYy
      · have hlo : ((((2751 * 2 ^ lowCfg.P / 5000 : ℕ) : ℤ)) : ℝ) / 2 ^ lowCfg.P ≤ y := by
          rw [Int.cast_natCast]
          have h1 : ((2751 * 2 ^ lowCfg.P / 5000 : ℕ) : ℝ) ≤ ((2751 * 2 ^ lowCfg.P : ℕ) : ℝ) / ((5000 : ℕ) : ℝ) :=
            Nat.cast_div_le
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat, Nat.cast_ofNat] at h1
          rw [div_le_iff₀ hP]
          have h2 : (2751 : ℝ) * 2 ^ lowCfg.P / 5000 ≤ y * 2 ^ lowCfg.P := by
            rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5000)]
            have := mul_lt_mul_of_pos_right hy' hP
            linarith
          linarith
        have hYe : y < (e : ℝ) / 2 ^ lowCfg.P := by
          have h' : ((((lowCfg.YT * 2 ^ lowCfg.P : ℕ) : ℤ)) : ℝ) ≤ (e : ℝ) := Int.cast_le.mpr hm
          rw [Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h'
          rw [lt_div_iff₀ hP]
          have := mul_lt_mul_of_pos_right hYy hP
          linarith
        obtain ⟨s, hs, h1, h2, hne, hpos⟩ := lcontigEnd_cover segs _ e he y hlo hYe
        exact lsegOK_sound lowCfg lowGroups lowCos lowP s (hsegs s hs) hne hpos lowCos_pos hch hord y h1 h2
    have hWy : lowCert.W y = 1 - lowCert.v y + lowCert.phihat y := rfl
    rw [hWy, lowCert_v]
    have := (abs_le.mp (hφ y)).1
    push_cast at hbound
    rw [add_div] at hbound
    linarith
  -- `|ρ| ≤ δ` on `[0, r]`
  have hρ : ∀ x ∈ Set.Icc 0 lowCert.r, |lowCert.rho x| ≤ (lowCfg.delta : ℝ) / 2 ^ lowCfg.P := by
    intro x hx
    have hx' : |x| ≤ 5502 / 10000 := by
      rw [abs_of_nonneg hx.1]
      have : x ≤ (2751 / 5000 : ℝ) := hx.2
      linarith
    have h1 := rhoOK_sound hr hch hord lowPsi_pos hx'
    have h2 := hφ x
    have e1 : lowCert.rho x = lowCert.phihat x - Tpoly (psiR lowPsi) 0 x := rfl
    have e2 : lowCert.r = 5502 / 10000 := by norm_num [lowCert]
    rw [e1]
    rw [e2] at h2
    calc |lowCert.phihat x - Tpoly (psiR lowPsi) 0 x| ≤ |lowCert.phihat x - PhatS lowCfg.P lowP x| +
          |PhatS lowCfg.P lowP x - Tpoly (psiR lowPsi) 0 x| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  -- the final inequality `2rδ < m(1 - κ)`
  have hfin : 2 * lowCert.r * ((lowCfg.delta : ℝ) / 2 ^ lowCfg.P) <
      (lowCfg.m : ℝ) / 2 ^ lowCfg.P * (1 - 9503 / 10000) := by
    simp only [lowCert, lowCfg, lowDelta, lowM]
    norm_num
  exact LCert.criterion hOk (κ := 9503 / 10000) (by norm_num) (by norm_num) kappa_r0 hW hρ hfin

/-- The non-strict lower bound (no extremizer needed): `0.5502² ≤ A₊(1)²` and `0.5502² ≤ C_{6.11}`. -/
theorem lower_weak_of (segs : List LSeg)
    (hbase : lbaseOK lowCfg lowGroups lowCos lowPsi lowP lowPSS segs = true)
    (hsegs : ∀ s ∈ segs, lsegOK lowCfg lowGroups lowCos lowP s = true) : LowerStatementWeak := by
  have hS := lower_Sr_of segs hbase hsegs
  have h1 := Aplus2_ge_of_Sr (r := 2751 / 5000) (κ := 9503 / 10000) (by norm_num) (by norm_num) (by norm_num)
    kappa_r0 hS
  exact ⟨h1, h1.trans Aplus2_le_C611⟩

/-- The strict lower bound under `ExtremizerHyp`. -/
theorem lower_strict_of (segs : List LSeg)
    (hbase : lbaseOK lowCfg lowGroups lowCos lowPsi lowP lowPSS segs = true)
    (hsegs : ∀ s ∈ segs, lsegOK lowCfg lowGroups lowCos lowP s = true) (hE : ExtremizerHyp) :
    ENNReal.ofReal ((2751 / 5000 : ℝ) ^ 2) < Aplus2 ∧ ENNReal.ofReal ((2751 / 5000 : ℝ) ^ 2) < C611 := by
  have hS := lower_Sr_of segs hbase hsegs
  have h1 := Aplus2_gt_of_Sr (by norm_num) hS hE
  exact ⟨h1, h1.trans_le Aplus2_le_C611⟩

/-- Theorem 1.1 from the lower checks, the upper half and `ExtremizerHyp`. -/
theorem main_of (segs : List LSeg)
    (hbase : lbaseOK lowCfg lowGroups lowCos lowPsi lowP lowPSS segs = true)
    (hsegs : ∀ s ∈ segs, lsegOK lowCfg lowGroups lowCos lowP s = true) (hup : UpperStatement)
    (hE : ExtremizerHyp) : MainStatement := by
  obtain ⟨h1, h2⟩ := lower_strict_of segs hbase hsegs hE
  exact ⟨h1, hup.1, h2, hup.2⟩

end SignUnc
