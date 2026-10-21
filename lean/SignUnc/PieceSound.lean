import SignUnc.JetSound4
import SignUnc.PolySound
import SignUnc.TaylorK

/-!
# Soundness of checker v4, part 6: `jetAll`, `omitAll`, `pieceOK4`, `runsOK`, `segOK4`

`segOK4_sound`: if `segOK4 c gs s = true` and the runs of `s` are non-empty with positive counts, then the
Gaussian combination of the groups is positive on `[s.lo, runsEnd s.lo s.ws]` (units `2^-P`).
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Finset

variable {P : ℕ}

/-! ## Sums over the groups -/

theorem jetAll_ok {n : ℕ} {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ {gs : List GGroup} {pgs : List PG4} {sps : List GSpec} {T : List Ball},
      List.Forall₂ (fun (g : GGroup) (G : PG4) => PG4Ok P G ∧ G.G.g = g) gs pgs →
      jetAll P n ex cz Y pgs sps = some T →
      MemL P ((List.range (n + 1)).map fun j => tauSum (inclAll gs sps) j y) T
  | [], [], [], T, List.Forall₂.nil, h => by
    simp only [jetAll, Option.some.injEq] at h
    subst h
    have : (fun j => tauSum (inclAll [] []) j y) = fun _ => (0 : ℝ) := by funext j; simp [inclAll, tauSum]
    rw [this]; exact memL_zeroL (n + 1)
  | [], [], _ :: _, T, List.Forall₂.nil, h => by simp [jetAll] at h
  | _ :: _, _ :: _, [], T, List.Forall₂.cons _ _, h => by simp [jetAll] at h
  | g :: gs, G :: pgs, sp :: sps, T, List.Forall₂.cons hG hgs, h => by
    simp only [jetAll, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    have h1 := groupJet_ok hex hcz hG.1 hY hA
    rw [hG.2] at h1
    have h2 := jetAll_ok hex hcz hY hgs hB
    have := memL_addL h1 h2
    rw [zipWith_add_range] at this
    convert this using 2
    funext j
    simp [inclAll, tauSum_append]

theorem omitAll_sound {n : ℕ} {ylo yhi : ℤ} {y : ℝ} (hy1 : (ylo : ℝ) / 2 ^ P ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ P) :
    ∀ {gs : List GGroup} {pgs : List PG4} {sps : List GSpec} {R : ℕ},
      List.Forall₂ (fun (g : GGroup) (G : PG4) => PG4Ok P G ∧ G.G.g = g) gs pgs →
      omitAll P n ylo yhi pgs sps = some R →
      |gsum (gs.flatMap GGroup.triples) y - tauSum (inclAll gs sps) 0 y| ≤ (R : ℝ) / 2 ^ P
  | [], [], [], R, List.Forall₂.nil, h => by
    simp only [omitAll, Option.some.injEq] at h
    subst h
    simp [gsum, inclAll, tauSum]
  | [], [], _ :: _, R, List.Forall₂.nil, h => by simp [omitAll] at h
  | _ :: _, _ :: _, [], R, List.Forall₂.cons _ _, h => by simp [omitAll] at h
  | g :: gs, G :: pgs, sp :: sps, R, List.Forall₂.cons hG hgs, h => by
    simp only [omitAll, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    have h1 := omitG_sound hG.1.hG ha hy1 hy2
    rw [hG.2] at h1
    have h2 := omitAll_sound hy1 hy2 hgs hb
    rw [List.flatMap_cons, gsum_append, inclAll, tauSum_append]
    have e : gsum g.triples y + gsum (gs.flatMap GGroup.triples) y - (tauSum (incl g sp) 0 y + tauSum (inclAll gs sps) 0 y) =
        (gsum g.triples y - tauSum (incl g sp) 0 y) + (gsum (gs.flatMap GGroup.triples) y - tauSum (inclAll gs sps) 0 y) := by
      ring
    rw [e]
    calc _ ≤ |gsum g.triples y - tauSum (incl g sp) 0 y| + |gsum (gs.flatMap GGroup.triples) y - tauSum (inclAll gs sps) 0 y| :=
          abs_add_le _ _
      _ ≤ (a : ℝ) / 2 ^ P + (b : ℝ) / 2 ^ P := add_le_add h1 h2
      _ = ((a + b : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

/-! ## Scaled coefficients and Horner evaluation -/

theorem memL_scaleEta {e : ℝ} {E : Ball} (hE : mem P e E) : ∀ (N : ℕ) {xR : ℕ → ℝ} {ts : List Ball} {p : ℝ} {pw : Ball},
    MemL P ((List.range N).map xR) ts → mem P p pw →
      MemL P ((List.range N).map fun j => xR j * (p * e ^ j)) (scaleEta P E ts pw)
  | 0, xR, ts, p, pw, h, _ => by cases h; simp [scaleEta]
  | N + 1, xR, ts, p, pw, h, hp => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map] at h
    cases h with
    | cons hx h' =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [scaleEta]
      refine List.Forall₂.cons (by simpa using mem_mul hx hp) ?_
      have := memL_scaleEta hE N (xR := xR ∘ Nat.succ) h' (mem_mul hp hE)
      convert this using 2
      funext j
      simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ]
      ring

/-- Horner evaluation of a list of reals. -/
noncomputable def hornR : List ℝ → ℝ → ℝ
  | [], _ => 0
  | v :: vs, σ => v + σ * hornR vs σ

theorem hornR_range (v : ℕ → ℝ) (σ : ℝ) : ∀ N, hornR ((List.range N).map v) σ = ∑ j ∈ range N, v j * σ ^ j := by
  intro N
  induction N generalizing v with
  | zero => simp [hornR]
  | succ N ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornR, ih, sum_range_succ', mul_sum]
    simp only [Function.comp_apply, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    refine sum_congr rfl (fun j _ => ?_); ring

theorem horn_close {σ : ℝ} (hσ : |σ| ≤ 1) : ∀ {vs : List ℝ} {bs : List Ball}, MemL P vs bs →
    |hornR vs σ - peval (bs.map (·.m)) σ / 2 ^ P| ≤ (((bs.map (·.r)).sum : ℕ) : ℝ) / 2 ^ P
  | [], [], List.Forall₂.nil => by simp [hornR]
  | v :: vs, b :: bs, List.Forall₂.cons hv h => by
    have ih := horn_close hσ h
    have hP : (0 : ℝ) < 2 ^ P := by positivity
    simp only [hornR, List.map_cons, peval_cons, List.sum_cons, Nat.cast_add]
    have e : v + σ * hornR vs σ - ((b.m : ℝ) + σ * peval (List.map (·.m) bs) σ) / 2 ^ P =
        (v - (b.m : ℝ) / 2 ^ P) + σ * (hornR vs σ - peval (List.map (·.m) bs) σ / 2 ^ P) := by ring
    rw [e, add_div]
    have hv' : |v - (b.m : ℝ) / 2 ^ P| ≤ (b.r : ℝ) / 2 ^ P := hv
    calc _ ≤ |v - (b.m : ℝ) / 2 ^ P| + |σ * (hornR vs σ - peval (List.map (·.m) bs) σ / 2 ^ P)| := abs_add_le _ _
      _ ≤ (b.r : ℝ) / 2 ^ P + (((bs.map (·.r)).sum : ℕ) : ℝ) / 2 ^ P := by
          refine add_le_add hv' ?_
          rw [abs_mul]
          exact le_trans (mul_le_of_le_one_left (abs_nonneg _) hσ) ih

theorem scaleEta_length (E : Ball) : ∀ (ts : List Ball) (pw : Ball), (scaleEta P E ts pw).length = ts.length
  | [], _ => rfl
  | _ :: ts, pw => by simp [scaleEta, scaleEta_length E ts]

/-! ## One piece -/

theorem pieceOK4_sound {n k m dm : ℕ} {gs : List GGroup} {pgs : List PG4} {sps : List GSpec} {R : ℕ} {lo : ℤ}
    {w : ℕ} (hF : List.Forall₂ (fun (g : GGroup) (G : PG4) => PG4Ok P G ∧ G.G.g = g) gs pgs)
    (h : pieceOK4 P n k m dm pgs sps R lo w = true) :
    ∀ y, (lo : ℝ) / 2 ^ P ≤ y → y ≤ ((lo + (w : ℤ) : ℤ) : ℝ) / 2 ^ P →
      (R : ℝ) / 2 ^ P < tauSum (inclAll gs sps) 0 y := by
  intro y hy1 hy2
  unfold pieceOK4 at h
  dsimp only at h
  split at h
  · rename_i T T' hT hT'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, hpoly⟩ := h
    set η := w - w / 2 with hη
    set y0 : ℤ := lo + ((w / 2 : ℕ) : ℤ) with hy0
    set L := inclAll gs sps
    have hP : (0 : ℝ) < 2 ^ P := by positivity
    set c : ℝ := (y0 : ℝ) / 2 ^ P with hc
    set er : ℝ := (η : ℝ) / 2 ^ P with her
    have her0 : 0 ≤ er := by positivity
    -- point jets at the centre
    have hJ := jetAll_ok (fun hx hX => mem_expB' hx hX) (fun hu hU => mem_cosSinTurn hu hU) (mem_point P y0) hF hT
    -- the remainder coefficient on the piece
    set M := (T'.getD (m + 1) ⟨0, 0⟩).absHi with hMdef
    have hM : ∀ x ∈ Set.Icc (c - er) (c + er), |tauSum L (m + 1) x| ≤ (M : ℝ) / 2 ^ P := by
      intro x hx
      have hxY : mem P x (⟨y0, η⟩ : Ball) := mem_center (by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
      have hJ' := jetAll_ok (fun hx hX => mem_expH hx hX) (fun hu hU => mem_cosSinTurnC hu hU) hxY hF hT'
      have hlen' : T'.length = m + 2 := by have := hJ'.length_eq; simp at this; omega
      have hmem := (List.forall₂_iff_get.mp hJ').2 (m + 1) (by simp) (by omega)
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at hmem
      rw [hMdef, List.getD_eq_getElem _ _ (by omega)]
      exact abs_le_absHi hmem
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
    -- Taylor
    have hTay := taylorK (m := m) (T := fun j => tauSum L j) (fun j _ x => hasDerivAt_tauSum L j x) hM y hy
    -- the normalized variable
    set σ : ℝ := if er = 0 then 0 else (y - c) / er with hσdef
    have hyc : |y - c| ≤ er := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have hσ1 : |σ| ≤ 1 := by
      rw [hσdef]; split_ifs with he
      · simp
      · rw [abs_div, abs_of_nonneg her0]
        exact div_le_one_of_le₀ hyc her0
    have hyσ : y - c = er * σ := by
      rw [hσdef]; split_ifs with he
      · rw [he] at hyc; have := abs_nonpos_iff.mp hyc; rw [this]; ring
      · field_simp
    -- npoly as a Horner sum of the scaled coefficients
    have hscale := memL_scaleEta (mem_point P (η : ℤ)) (m + 1) hJ (by simpa using mem_ofInt P 1)
    set bs := scaleEta P ⟨(η : ℤ), 0⟩ T (ofInt P 1) with hbs
    have hnp : npoly (fun j => tauSum L j) c m y =
        hornR ((List.range (m + 1)).map fun j => tauSum L j c * (1 * (((η : ℤ) : ℝ) / 2 ^ P) ^ j)) σ := by
      rw [hornR_range, npoly]
      refine sum_congr rfl (fun j _ => ?_)
      rw [hyσ, mul_pow]; push_cast; ring
    have hclose := horn_close hσ1 hscale
    have hblen : (bs.map (·.m)).length = m + 1 := by simp [hbs, scaleEta_length, hlen]
    have hK := polyOK_top hblen hpoly hσ1
    -- assemble
    have hrem : (M : ℝ) / 2 ^ P * |y - c| ^ (m + 1) ≤
        ((cdiv (M * η ^ (m + 1)) (2 ^ (P * (m + 1))) : ℕ) : ℝ) / 2 ^ P := by
      have h1 : |y - c| ^ (m + 1) ≤ er ^ (m + 1) := pow_le_pow_left₀ (abs_nonneg _) hyc (m + 1)
      have h2 := cdiv_spec (M * η ^ (m + 1)) (2 ^ (P * (m + 1))) (by positivity)
      have h3 : (M : ℝ) / 2 ^ P * er ^ (m + 1) = ((M * η ^ (m + 1) : ℕ) : ℝ) / ((2 ^ (P * (m + 1)) : ℕ) : ℝ) / 2 ^ P := by
        rw [her]; push_cast; rw [pow_mul, div_pow]; field_simp
      calc (M : ℝ) / 2 ^ P * |y - c| ^ (m + 1) ≤ (M : ℝ) / 2 ^ P * er ^ (m + 1) := by gcongr
        _ = ((M * η ^ (m + 1) : ℕ) : ℝ) / ((2 ^ (P * (m + 1)) : ℕ) : ℝ) / 2 ^ P := h3
        _ ≤ ((cdiv (M * η ^ (m + 1)) (2 ^ (P * (m + 1))) : ℕ) : ℝ) / 2 ^ P := by gcongr
    have hT1 := (abs_le.mp hTay).1
    have hc2 := (abs_le.mp hclose).1
    rw [hnp] at hT1
    have hlist : ((List.range (m + 1)).map fun j => tauSum L j c * (1 * (((η : ℤ) : ℝ) / 2 ^ P) ^ j)) =
        ((List.range (m + 1)).map fun j => tauSum (inclAll gs sps) j ((y0 : ℝ) / 2 ^ P) *
          (1 * (((η : ℤ) : ℝ) / 2 ^ P) ^ j)) := rfl
    rw [hlist] at hT1
    have hKr := div_lt_div_of_pos_right hK hP
    rw [Nat.cast_add, Nat.cast_add, add_div, add_div] at hKr
    have hTL : tauSum L 0 y = tauSum (inclAll gs sps) 0 y := rfl
    rw [← hTL]
    linarith
  · exact absurd h (by simp)

/-! ## Runs and segments -/

theorem runOK_sound {n k m dm : ℕ} {gs : List GGroup} {pgs : List PG4} {sps : List GSpec} {R w : ℕ}
    (hF : List.Forall₂ (fun (g : GGroup) (G : PG4) => PG4Ok P G ∧ G.G.g = g) gs pgs) :
    ∀ (cnt : ℕ) (lo : ℤ), 0 < cnt → runOK P n k m dm pgs sps R w cnt lo = true →
      ∀ y, (lo : ℝ) / 2 ^ P ≤ y → y ≤ ((lo + ((w * cnt : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P →
        (R : ℝ) / 2 ^ P < tauSum (inclAll gs sps) 0 y := by
  intro cnt
  induction cnt with
  | zero => intro lo h; omega
  | succ c ih =>
    intro lo _ h y hy1 hy2
    simp only [runOK, Bool.and_eq_true] at h
    obtain ⟨hp, hr⟩ := h
    rcases le_or_gt y (((lo + (w : ℤ) : ℤ) : ℝ) / 2 ^ P) with hle | hgt
    · exact pieceOK4_sound hF hp y hy1 hle
    · rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · subst hc0
        simp only [zero_add, mul_one] at hy2
        exact absurd hy2 (not_le.mpr hgt)
      · refine ih (lo + (w : ℤ)) hc0 hr y hgt.le ?_
        convert hy2 using 3
        push_cast; ring

theorem runsOK_sound {n k m dm : ℕ} {gs : List GGroup} {pgs : List PG4} {sps : List GSpec} {R : ℕ}
    (hF : List.Forall₂ (fun (g : GGroup) (G : PG4) => PG4Ok P G ∧ G.G.g = g) gs pgs) :
    ∀ (ws : List (ℕ × ℕ)) (lo : ℤ), ws ≠ [] → (∀ r ∈ ws, 0 < r.2) → runsOK P n k m dm pgs sps R lo ws = true →
      ∀ y, (lo : ℝ) / 2 ^ P ≤ y → y ≤ (runsEnd lo ws : ℝ) / 2 ^ P →
        (R : ℝ) / 2 ^ P < tauSum (inclAll gs sps) 0 y := by
  intro ws
  induction ws with
  | nil => intro _ h; exact absurd rfl h
  | cons r rs ih =>
    intro lo _ hpos h y hy1 hy2
    obtain ⟨w, cnt⟩ := r
    simp only [runsOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hc : 0 < cnt := hpos (w, cnt) (by simp)
    rcases le_or_gt y (((lo + ((w * cnt : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P) with hle | hgt
    · exact runOK_sound hF cnt lo hc h1 y hy1 hle
    · cases rs with
      | nil =>
        simp only [runsEnd, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hy2
        exact absurd hy2 (not_le.mpr hgt)
      | cons r' rs' =>
        refine ih _ (by simp) (fun r hr => hpos r (by simp [hr])) h2 y hgt.le ?_
        convert hy2 using 2
        simp only [runsEnd, List.map_cons, List.sum_cons]
        push_cast; ring

theorem segOK4_sound (c : Cfg) (gs : List GGroup) (s : Seg4) (h : segOK4 c gs s = true)
    (hne : s.ws ≠ []) (hpos : ∀ r ∈ s.ws, 0 < r.2) :
    ∀ y, (s.lo : ℝ) / 2 ^ c.P ≤ y → y ≤ (runsEnd s.lo s.ws : ℝ) / 2 ^ c.P →
      0 < gsum (gs.flatMap GGroup.triples) y := by
  intro y hy1 hy2
  unfold segOK4 at h
  split at h
  · rename_i pgs hpgs
    split at h
    · rename_i R hR
      have hF := prepGroups4_ok hpgs
      have hom := omitAll_sound hy1 hy2 hF hR
      have hrun := runsOK_sound hF s.ws s.lo hne hpos h y hy1 hy2
      have := (abs_le.mp hom).1
      linarith
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end SignUnc.Chk
