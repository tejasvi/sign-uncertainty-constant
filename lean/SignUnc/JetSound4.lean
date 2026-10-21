import SignUnc.OmitSound

/-!
# Soundness of checker v4, part 5: `groupJet` and `jetAll`

`groupJet_ok`: entry `j` of `groupJet … G sp Y` contains `tauSum (incl g sp) j y` for every `y` in the ball `Y`
(the normalized Taylor coefficients of the included terms); `jetAll_ok` sums the groups.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex Finset

variable {P : ℕ}

/-! ## Prepared groups of checker v4 -/

/-- Facts about a prepared group of checker v4. -/
structure PG4Ok (P : ℕ) (G : PG4) : Prop where
  hG : PGOk P G.G
  hOM : List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball × Ball) =>
    mem P r.1 b.1 ∧ mem P (2 * π * r.2) b.2.1 ∧ mem P (-((2 * π * r.2) * (2 * π * r.2))) b.2.2) G.G.g.csR G.OM

theorem prepGroup_g {n : ℕ} {g : GGroup} {G : PG} (h : prepGroup P n g = some G) : G.g = g := by
  unfold prepGroup at h
  split_ifs at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

theorem prepGroup4_ok {n : ℕ} {g : GGroup} {G : PG4} (h : prepGroup4 P n g = some G) :
    PG4Ok P G ∧ G.G.g = g := by
  unfold prepGroup4 at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨G0, hG0, rfl⟩ := h
  have hok := prepGroup_ok hG0
  refine ⟨⟨hok, ?_⟩, prepGroup_g hG0⟩
  have h2pi := mem_mulInt 2 (mem_piB P)
  have hCS := hok.hCS
  simp only
  rw [List.forall₂_map_right_iff]
  refine hCS.imp (fun r b hrb => ⟨hrb.1, ?_, ?_⟩)
  · have := mem_mul h2pi hrb.2; push_cast at this; exact this
  · have h1 := mem_mul h2pi hrb.2
    have := mem_neg (mem_mul h1 h1); push_cast at this; exact this

theorem prepGroups4_ok {n : ℕ} : ∀ {L : List GGroup} {pgs : List PG4}, prepGroups4 P n L = some pgs →
    List.Forall₂ (fun (g : GGroup) (G : PG4) => PG4Ok P G ∧ G.G.g = g) L pgs
  | [], pgs, h => by simp [prepGroups4] at h; subst h; exact List.Forall₂.nil
  | g :: L, pgs, h => by
    simp only [prepGroups4, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨G, hG, Gs, hGs, rfl⟩ := h
    exact List.Forall₂.cons (prepGroup4_ok hG) (prepGroups4_ok hGs)

/-! ## List helpers -/

theorem forall₂_zipWith {α β γ δ ε ζ : Type*} {R1 : α → β → Prop} {R2 : γ → δ → Prop} {R3 : ε → ζ → Prop}
    {f : α → γ → ε} {f' : β → δ → ζ} (hf : ∀ a b c d, R1 a b → R2 c d → R3 (f a c) (f' b d)) :
    ∀ {l1 : List α} {l1' : List β} {l2 : List γ} {l2' : List δ}, List.Forall₂ R1 l1 l1' → List.Forall₂ R2 l2 l2' →
      List.Forall₂ R3 (List.zipWith f l1 l2) (List.zipWith f' l1' l2')
  | [], [], _, _, List.Forall₂.nil, _ => by simp
  | _ :: _, _ :: _, [], [], List.Forall₂.cons _ _, List.Forall₂.nil => by simp
  | _ :: _, _ :: _, _ :: _, _ :: _, List.Forall₂.cons h1 t1, List.Forall₂.cons h2 t2 => by
    simp only [List.zipWith_cons_cons]
    exact List.Forall₂.cons (hf _ _ _ _ h1 h2) (forall₂_zipWith hf t1 t2)

theorem forall₂_drop {α β : Type*} {R : α → β → Prop} : ∀ (n : ℕ) {l : List α} {l' : List β},
    List.Forall₂ R l l' → List.Forall₂ R (l.drop n) (l'.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], List.Forall₂.nil => by simp
  | n + 1, _ :: _, _ :: _, List.Forall₂.cons _ t => by simpa using forall₂_drop n t

theorem forall₂_map_zipWith {α β γ ε ζ : Type*} {R1 : α → β → Prop} {R2 : α → γ → Prop} {R3 : ε → ζ → Prop}
    {f : α → ε} {f' : β → γ → ζ} (hf : ∀ a b c, R1 a b → R2 a c → R3 (f a) (f' b c)) :
    ∀ {l : List α} {l1 : List β} {l2 : List γ}, List.Forall₂ R1 l l1 → List.Forall₂ R2 l l2 →
      List.Forall₂ R3 (l.map f) (List.zipWith f' l1 l2)
  | [], [], [], List.Forall₂.nil, List.Forall₂.nil => by simp
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons h1 t1, List.Forall₂.cons h2 t2 => by
    simp only [List.map_cons, List.zipWith_cons_cons]
    exact List.Forall₂.cons (hf _ _ _ h1 h2) (forall₂_map_zipWith hf t1 t2)

theorem memL_map_mul {q : ℝ} {Q : Ball} (hq : mem P q Q) : ∀ {xs : List ℝ} {L : List Ball}, MemL P xs L →
    MemL P (xs.map (q * ·)) (L.map (mul P Q))
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => List.Forall₂.cons (mem_mul hq h) (memL_map_mul hq t)

theorem memL_of_getElem {xs : ℕ → ℝ} {m : ℕ} {L : List Ball} (hlen : L.length = m)
    (h : ∀ i (hi : i < L.length), mem P (xs i) L[i]) : MemL P ((List.range m).map xs) L := by
  apply List.forall₂_of_length_eq_of_get (by simp [hlen])
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact h i h2

/-- A row list zipped with values indexed by the row positions. -/
theorem zipWith_range_eq {X : Type*} (l : List (ℝ × ℝ)) (σ : ℕ → ℝ) (hl : ∀ i (hi : i < l.length), (l[i]).2 = σ i)
    (φ : ℝ → ℝ) (F : ℝ × ℝ → ℝ → X) (m : ℕ) :
    List.zipWith F l ((List.range m).map fun i => φ (σ i)) = (l.take m).map fun r => F r (φ r.2) := by
  apply List.ext_getElem (by simp [Nat.min_comm])
  intro i h1 h2
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_take]
  have hi : i < l.length := by simp at h1; omega
  rw [hl i hi]

theorem csR_drop_snd (g : GGroup) (k1 : ℕ) : ∀ i (hi : i < (g.csR.drop k1).length), ((g.csR.drop k1)[i]).2 = sR g (k1 + i) := by
  intro i hi
  rw [List.getElem_drop]
  exact csR_getElem_snd g _ (by simp at hi; omega)

theorem csR_snd (g : GGroup) : ∀ i (hi : i < g.csR.length), (g.csR[i]).2 = sR g i := fun i hi => csR_getElem_snd g i hi

/-! ## The jets of a group -/

/-- Real rows of the E-moments. -/
noncomputable def rowsE (g : GGroup) (sp : GSpec) (y : ℝ) : List (ℝ × ℝ) :=
  ((g.csR.drop sp.k1).take (sp.k2 - sp.k1)).map fun r =>
    (r.1 * Real.exp (-π * aR g * (y - r.2) ^ 2), -(2 * (π * aR g)) * (y - r.2))

/-- Real rows of the F-moments. -/
noncomputable def rowsF (g : GGroup) (sp : GSpec) (y : ℝ) : List (ℝ × ℝ) :=
  (g.csR.take sp.kF).map fun r =>
    (r.1 * Real.exp (-π * aR g * (y + r.2) ^ 2), -(2 * (π * aR g)) * (y + r.2))

/-- Real rows of the H-moments. -/
noncomputable def rowsH (g : GGroup) (y : ℝ) : List (ℝ × ℝ × ℝ) :=
  g.csR.map fun r => (r.1 * Real.cos (2 * π * r.2 * y), -((2 * π * r.2) * (r.1 * Real.sin (2 * π * r.2 * y))),
    -((2 * π * r.2) * (2 * π * r.2)))

theorem tauSum_inclE (g : GGroup) (sp : GSpec) (j : ℕ) (y : ℝ) :
    tauSum (inclE g sp) j y = ∑ p ∈ range (j + 1), momR (rowsE g sp y) p / (p.factorial : ℝ) * ecoef 0 (-(π * aR g)) (j - p) := by
  rw [← listSum_ecoef, tauSum_eq, inclE, rowsE, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply]
  rw [tau_quadE]

theorem tauSum_inclF (g : GGroup) (sp : GSpec) (j : ℕ) (y : ℝ) :
    tauSum (inclF g sp) j y = ∑ p ∈ range (j + 1), momR (rowsF g sp y) p / (p.factorial : ℝ) * ecoef 0 (-(π * aR g)) (j - p) := by
  rw [← listSum_ecoef, tauSum_eq, inclF, rowsF, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply]
  rw [tau_quadF]

theorem tauSum_inclH_hz (g : GGroup) (sp : GSpec) (hz : sp.hz = true) (j : ℕ) (y : ℝ) :
    tauSum (inclH g sp) j y = 2 / Real.sqrt (aR g) * Real.exp (-π * y ^ 2 / aR g) *
      ∑ p ∈ range (j + 1), momR2 (rowsH g y) p / (p.factorial : ℝ) *
        ecoef (-(2 * π * (y * (1 / aR g)))) (-(π * (1 / aR g))) (j - p) := by
  rw [← listSum_pw2, ← List.sum_map_mul_left]
  unfold inclH
  rw [if_pos hz, tauSum_eq, rowsH, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply]
  rw [tau_quadH]

theorem tauSum_inclH_nhz (g : GGroup) (sp : GSpec) (hz : sp.hz = false) (j : ℕ) (y : ℝ) :
    tauSum (inclH g sp) j y = 0 := by
  unfold inclH; rw [if_neg (by simp [hz])]; simp [tauSum]

theorem tauSum_incl (g : GGroup) (sp : GSpec) (j : ℕ) (y : ℝ) :
    tauSum (incl g sp) j y = tauSum (inclE g sp) j y + tauSum (inclF g sp) j y + tauSum (inclH g sp) j y := by
  rw [incl, tauSum_append, tauSum_append]

theorem groupJet_ok {n : ℕ} {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {G : PG4} (hG : PG4Ok P G) {y : ℝ} {Y : Ball} (hY : mem P y Y) {sp : GSpec} {T : List Ball}
    (h : groupJet P n ex cz G sp Y = some T) :
    MemL P ((List.range (n + 1)).map fun j => tauSum (incl G.G.g sp) j y) T := by
  have hPG := hG.hG
  set g := G.G.g with hgdef
  set a := aR g
  unfold groupJet at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨Es, hEs, Fs, hFs, h⟩ := h
  obtain ⟨hEl, hE⟩ := gridE_ok hex hPG hY hEs
  obtain ⟨hFl, hF⟩ := gridF_ok hex hPG hY hFs
  have htpa : mem P (2 * (π * a)) (mulInt 2 G.G.pa) := by
    have := mem_mulInt 2 hPG.hpa; push_cast at this; exact this
  -- E moments
  have hmE : MemL P ((List.range (n + 1)).map (momR (rowsE g sp y)))
      (momE P n (mulInt 2 G.G.pa) Y (G.G.CS.drop sp.k1) Es) := by
    have hEs' : MemL P ((List.range (sp.k2 - sp.k1)).map fun i => Real.exp (-π * a * (y - sR g (sp.k1 + i)) ^ 2)) Es :=
      memL_of_getElem hEl hE
    have hz := forall₂_zipWith (R3 := fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2)
      (f := fun (r : ℝ × ℝ) (e : ℝ) => (r.1 * e, -(2 * (π * a)) * (y - r.2)))
      (f' := fun (r : Ball × Ball) (E : Ball) => (mul P r.1 E, neg (mul P (mulInt 2 G.G.pa) (sub Y r.2))))
      (fun r b e E hrb he => ⟨mem_mul hrb.1 he, by
        have := mem_neg (mem_mul htpa (mem_sub hY hrb.2)); rw [neg_mul_eq_neg_mul] at this; exact this⟩)
      (forall₂_drop sp.k1 hPG.hCS) hEs'
    have heq := zipWith_range_eq (g.csR.drop sp.k1) (fun i => sR g (sp.k1 + i)) (csR_drop_snd g sp.k1)
      (fun s => Real.exp (-π * a * (y - s) ^ 2)) (fun r e => (r.1 * e, -(2 * (π * a)) * (y - r.2))) (sp.k2 - sp.k1)
    rw [heq] at hz
    exact memL_momW n hz
  -- F moments
  have hmF : MemL P ((List.range (n + 1)).map (momR (rowsF g sp y)))
      (momF P n (mulInt 2 G.G.pa) Y G.G.CS Fs) := by
    have hFs' : MemL P ((List.range sp.kF).map fun i => Real.exp (-π * a * (y + sR g i) ^ 2)) Fs :=
      memL_of_getElem hFl hF
    have hz := forall₂_zipWith (R3 := fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2)
      (f := fun (r : ℝ × ℝ) (e : ℝ) => (r.1 * e, -(2 * (π * a)) * (y + r.2)))
      (f' := fun (r : Ball × Ball) (F : Ball) => (mul P r.1 F, neg (mul P (mulInt 2 G.G.pa) (add Y r.2))))
      (fun r b e E hrb he => ⟨mem_mul hrb.1 he, by
        have := mem_neg (mem_mul htpa (mem_add hY hrb.2)); rw [neg_mul_eq_neg_mul] at this; exact this⟩)
      hPG.hCS hFs'
    have heq := zipWith_range_eq g.csR (fun i => sR g i) (csR_snd g)
      (fun s => Real.exp (-π * a * (y + s) ^ 2)) (fun r e => (r.1 * e, -(2 * (π * a)) * (y + r.2))) sp.kF
    rw [heq] at hz
    exact memL_momW n hz
  -- the E/F part
  have hAdd := memL_addL hmE hmF
  rw [zipWith_add_range] at hAdd
  have hEF := memL_divFact hAdd
  have hg := memL_eser (P := P) (α := 0) (β := -(π * a)) (al := ⟨0, 0⟩) (be := neg G.G.pa) mem_zero_ball
    (mem_neg hPG.hpa) n
  have htE := memL_conv hEF hg
  have hEFsum : ∀ j, tauSum (inclE g sp) j y + tauSum (inclF g sp) j y =
      ∑ p ∈ range (j + 1), (momR (rowsE g sp y) p + momR (rowsF g sp y) p) / (p.factorial : ℝ) *
        ecoef 0 (-(π * a)) (j - p) := by
    intro j
    rw [tauSum_inclE, tauSum_inclF, ← sum_add_distrib]
    refine sum_congr rfl (fun p _ => ?_)
    ring
  cases hzc : sp.hz with
  | false =>
    rw [hzc] at h
    simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
    subst h
    convert htE using 2
    funext j
    rw [tauSum_incl, tauSum_inclH_nhz g sp hzc, add_zero, hEFsum]
  | true =>
    rw [hzc] at h
    simp only [if_true, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨QH, Zs⟩, hHZ, rfl⟩ := h
    obtain ⟨hQH, hZl, hZ⟩ := gridH_ok hex hcz hPG hY hHZ
    -- H moments
    have hZs : List.Forall₂ (fun (r : ℝ × ℝ) (Z : CDisc) => memC P (Complex.exp ((2 * π * (r.2 * y) : ℝ) * I)) Z)
        g.csR Zs := forall₂_csR g Zs (fun sv z => memC P (Complex.exp ((2 * π * (sv * y) : ℝ) * I)) z) hZl hZ
    have hz := forall₂_map_zipWith (R3 := fun (r : ℝ × ℝ × ℝ) (b : Ball × Ball × Ball) =>
        mem P r.1 b.1 ∧ mem P r.2.1 b.2.1 ∧ mem P r.2.2 b.2.2)
      (f := fun (r : ℝ × ℝ) => (r.1 * Real.cos (2 * π * r.2 * y),
        -((2 * π * r.2) * (r.1 * Real.sin (2 * π * r.2 * y))), -((2 * π * r.2) * (2 * π * r.2))))
      (f' := fun (r : Ball × Ball × Ball) (Z : CDisc) => (mul P r.1 Z.re, neg (mul P r.2.1 (mul P r.1 Z.im)), r.2.2))
      (fun r b Z hrb hZr => by
        have hre := mem_re hZr
        have him := mem_im hZr
        rw [Complex.exp_ofReal_mul_I_re] at hre
        rw [Complex.exp_ofReal_mul_I_im] at him
        rw [show 2 * π * (r.2 * y) = 2 * π * r.2 * y by ring] at hre him
        exact ⟨mem_mul hrb.1 hre, mem_neg (mem_mul hrb.2.1 (mem_mul hrb.1 him)), hrb.2.2⟩)
      hG.hOM hZs
    have hmH : MemL P ((List.range (n + 1)).map (momR2 (rowsH g y))) (momH P n G.OM Zs) := memL_momW2 n hz
    have hgH := memL_eser (P := P) (α := -(2 * π * (y * (1 / a)))) (β := -(π * (1 / a)))
      (al := neg (mul P (mulInt 2 (piB P)) (mul P Y G.G.Ai))) (be := neg (mul P (piB P) G.G.Ai))
      (by have := mem_neg (mem_mul (mem_mulInt 2 (mem_piB P)) (mem_mul hY hPG.hAi)); push_cast at this; exact this)
      (mem_neg (mem_mul (mem_piB P) hPG.hAi)) n
    have htH := memL_map_mul hQH (memL_conv (memL_divFact hmH) hgH)
    have hT := memL_addL htE htH
    rw [List.map_map, zipWith_add_range] at hT
    convert hT using 2
    funext j
    simp only [Function.comp_apply]
    rw [tauSum_incl, hEFsum, tauSum_inclH_hz g sp hzc]

end SignUnc.Chk
