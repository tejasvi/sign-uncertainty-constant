import SignUnc.JetSound

/-!
# Soundness of checker v4, part 2: the grid lists on index ranges
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex Finset

variable {P : ℕ}

/-- From index facts to relations along a sublist of `csR`. -/
theorem forall₂_csR_sub {α : Type*} (g : GGroup) (k1 m : ℕ) (l : List α) (R : ℝ → α → Prop)
    (hlen : l.length = m) (hm : k1 + m ≤ g.cs.length) (h : ∀ i (hi : i < l.length), R (sR g (k1 + i)) l[i]) :
    List.Forall₂ (fun (r : ℝ × ℝ) (x : α) => R r.2 x) ((g.csR.drop k1).take m) l := by
  apply List.forall₂_of_length_eq_of_get (by simp [csR_length, hlen]; omega)
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_take, List.getElem_drop]
  rw [csR_getElem_snd g (k1 + i) (by rw [csR_length]; simp at h1; omega)]
  exact h i h2

theorem gridE_ok {ex : Ball → Option Ball}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    {G : PG} (hG : PGOk P G) {y : ℝ} {Y : Ball} (hY : mem P y Y) {k1 k2 : ℕ} {Es : List Ball}
    (h : gridE P ex G Y k1 k2 = some Es) :
    Es.length = k2 - k1 ∧
      ∀ i (hi : i < Es.length), mem P (Real.exp (-π * aR G.g * (y - sR G.g (k1 + i)) ^ 2)) Es[i] := by
  unfold gridE at h
  split_ifs at h with hk
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨Ek, hEk, Rup, hRup, Rdn, hRdn, hEs⟩ := h
    set g := G.g
    set ks := min (max (kStar P g Y) k1) (k2 - 1) with hks_def
    have hks1 : k1 ≤ ks := by simp only [ks]; omega
    have hks2 : ks < k2 := by simp only [ks]; omega
    set a := aR g
    set Δ := dR g
    have hu : mem P (y - sR g ks) (sub Y (ofRat P (g.sk ks).1 (g.sk ks).2)) := by
      have := mem_ofRat P (g.sk ks).1 (g.sk ks).2 (by unfold GGroup.sk; have := hG.hs0d; have := hG.hdd; positivity)
      rw [sk_eq g hG.hs0d hG.hdd ks] at this
      exact mem_sub hY this
    set u := y - sR g ks
    have h2paD : mem P ((2 : ℤ) * (π * a) * Δ) (mul P (mulInt 2 G.pa) G.D) :=
      mem_mul (mem_mulInt 2 hG.hpa) hG.hD
    have hpaD2 : mem P (π * a * (Δ * Δ)) (mul P G.pa (mul P G.D G.D)) := mem_mul hG.hpa (mem_mul hG.hD hG.hD)
    have hEk' : mem P (Real.exp (-π * a * u ^ 2)) Ek := by
      have := hex (mem_neg (mem_mul hG.hpa (mem_mul hu hu))) hEk
      rwa [show -(π * a * (u * u)) = -π * a * u ^ 2 by ring] at this
    have hRup' : mem P (Real.exp (2 * π * a * Δ * u - π * a * Δ ^ 2)) Rup := by
      have := hex (mem_sub (mem_mul h2paD hu) hpaD2) hRup
      rwa [show (2 : ℤ) * (π * a) * Δ * u - π * a * (Δ * Δ) = 2 * π * a * Δ * u - π * a * Δ ^ 2 by
        push_cast; ring] at this
    have hRdn' : mem P (Real.exp (2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2)) Rdn := by
      have := hex (mem_sub (mem_neg (mem_mul h2paD hu)) hpaD2) hRdn
      rwa [show -((2 : ℤ) * (π * a) * Δ * u) - π * a * (Δ * Δ) = 2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2 by
        push_cast; ring] at this
    have hrho' : mem P (Real.exp (-2 * π * a * (-Δ) ^ 2)) G.rho := by
      rw [neg_sq]; exact hG.hrho
    have hx1 : mem P (Real.exp (-π * a * (u - (-Δ)) ^ 2)) (mul P Ek Rdn) := by
      have := mem_mul hEk' hRdn'
      rwa [← Real.exp_add, show -π * a * u ^ 2 + (2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2) =
        -π * a * (u - (-Δ)) ^ 2 by ring] at this
    have hr1 : mem P (Real.exp (2 * π * a * (-Δ) * (u - (-Δ)) - π * a * (-Δ) ^ 2)) (mul P Rdn G.rho) := by
      have := mem_mul hRdn' hrho'
      rwa [← Real.exp_add, show 2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2 + -2 * π * a * (-Δ) ^ 2 =
        2 * π * a * (-Δ) * (u - (-Δ)) - π * a * (-Δ) ^ 2 by ring] at this
    have hlen1 : (recList P G.rho (ks - k1) (mul P Ek Rdn) (mul P Rdn G.rho)).reverse.length = ks - k1 := by
      simp [recList_length]
    refine ⟨by rw [← hEs]; simp [recList_length]; omega, ?_⟩
    intro i hi
    subst hEs
    by_cases hlt : i < ks - k1
    · rw [List.getElem_append_left (by rw [hlen1]; exact hlt), List.getElem_reverse]
      have hj : ks - k1 - 1 - i < ks - k1 := by omega
      have := recList_getElem hrho' hx1 hr1 (ks - k1 - 1 - i) hj
      have hsk : sR g ks = sR g (k1 + i) + (((ks - k1 - 1 - i : ℕ) : ℝ) + 1) * Δ := by
        have h0 := sR_succ g (k1 + i) (ks - k1 - 1 - i + 1)
        rw [show k1 + i + (ks - k1 - 1 - i + 1) = ks by omega] at h0
        rw [h0]; push_cast; ring
      have e : u - -Δ - ((ks - k1 - 1 - i : ℕ) : ℝ) * -Δ = y - sR g (k1 + i) := by
        simp only [u]; rw [hsk]; ring
      rw [e] at this
      simpa [recList_length] using this
    · rw [List.getElem_append_right (by rw [hlen1]; omega)]
      have hi2 : i < (ks - k1) + (k2 - ks) := by
        have := hi; simp [recList_length] at this; omega
      have hj : i - (ks - k1) < k2 - ks := by omega
      have := recList_getElem hG.hrho hEk' hRup' (i - (ks - k1)) hj
      have hsk : sR g (k1 + i) = sR g ks + ((i - (ks - k1) : ℕ) : ℝ) * Δ := by
        have h0 := sR_succ g ks (i - (ks - k1))
        rw [show ks + (i - (ks - k1)) = k1 + i by omega] at h0
        exact h0
      have e : u - ((i - (ks - k1) : ℕ) : ℝ) * Δ = y - sR g (k1 + i) := by
        simp only [u]; rw [hsk]; ring
      rw [e] at this
      simpa [hlen1] using this
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨by simp; omega, fun i hi => absurd hi (by simp)⟩

theorem gridF_ok {ex : Ball → Option Ball}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    {G : PG} (hG : PGOk P G) {y : ℝ} {Y : Ball} (hY : mem P y Y) {kF : ℕ} {Fs : List Ball}
    (h : gridF P ex G Y kF = some Fs) :
    Fs.length = kF ∧ ∀ i (hi : i < Fs.length), mem P (Real.exp (-π * aR G.g * (y + sR G.g i) ^ 2)) Fs[i] := by
  unfold gridF at h
  split_ifs at h with hk
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨F0, hF0, T0, hT0, hFs⟩ := h
    set g := G.g
    set a := aR g
    set Δ := dR g
    have hv0 : mem P (y + sR g 0) (add Y G.S0) := mem_add hY hG.hS0
    have h2paD : mem P ((2 : ℤ) * (π * a) * Δ) (mul P (mulInt 2 G.pa) G.D) :=
      mem_mul (mem_mulInt 2 hG.hpa) hG.hD
    have hpaD2 : mem P (π * a * (Δ * Δ)) (mul P G.pa (mul P G.D G.D)) := mem_mul hG.hpa (mem_mul hG.hD hG.hD)
    have hF0' : mem P (Real.exp (-π * a * (y + sR g 0) ^ 2)) F0 := by
      have := hex (mem_neg (mem_mul hG.hpa (mem_mul hv0 hv0))) hF0
      rwa [show -(π * a * ((y + sR g 0) * (y + sR g 0))) = -π * a * (y + sR g 0) ^ 2 by ring] at this
    have hT0' : mem P (Real.exp (2 * π * a * (-Δ) * (y + sR g 0) - π * a * (-Δ) ^ 2)) T0 := by
      have := hex (mem_sub (mem_neg (mem_mul h2paD hv0)) hpaD2) hT0
      rwa [show -((2 : ℤ) * (π * a) * Δ * (y + sR g 0)) - π * a * (Δ * Δ) =
        2 * π * a * (-Δ) * (y + sR g 0) - π * a * (-Δ) ^ 2 by push_cast; ring] at this
    have hrho' : mem P (Real.exp (-2 * π * a * (-Δ) ^ 2)) G.rho := by
      rw [neg_sq]; exact hG.hrho
    subst hFs
    refine ⟨recList_length _ _ _ _, ?_⟩
    intro i hi
    have hi' : i < kF := by simpa [recList_length] using hi
    have := recList_getElem hrho' hF0' hT0' i hi'
    have hsk : sR g i = sR g 0 + (i : ℝ) * Δ := by
      have h0 := sR_succ g 0 i
      rwa [zero_add] at h0
    have e : y + sR g 0 - (i : ℝ) * -Δ = y + sR g i := by rw [hsk]; ring
    rw [e] at this
    exact this
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨by simp; omega, fun i hi => absurd hi (by simp)⟩

theorem gridH_ok {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {G : PG} (hG : PGOk P G) {y : ℝ} {Y : Ball} (hY : mem P y Y) {QH : Ball} {Zs : List CDisc}
    (h : gridH P ex cz G Y = some (QH, Zs)) :
    mem P (2 / Real.sqrt (aR G.g) * Real.exp (-π * y ^ 2 / aR G.g)) QH ∧ Zs.length = G.g.cs.length ∧
      ∀ k (hk : k < Zs.length), memC P (Complex.exp ((2 * π * (sR G.g k * y) : ℝ) * I)) Zs[k] := by
  unfold gridH at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨H, hH, ⟨Z0c, Z0s⟩, hZ0, ⟨Wc, Ws⟩, hW, hQH, hZs⟩ := h
  set g := G.g
  set a := aR g
  set Δ := dR g
  have hH' : mem P (Real.exp (-π * y ^ 2 / a)) H := by
    have := hex (mem_neg (mem_mul (mem_piB P) (mem_mul (mem_mul hY hY) hG.hAi))) hH
    rwa [show -(π * (y * y * (1 / a))) = -π * y ^ 2 / a by ring] at this
  refine ⟨by subst hQH; exact mem_mul hG.hQ hH', by rw [← hZs, powList_length], ?_⟩
  intro k hk
  subst hZs
  have hk' : k < g.cs.length := by simpa [powList_length] using hk
  have hcz0 := hcz (mem_mul hG.hS0 hY) hZ0
  have hcw := hcz (mem_mul hG.hD hY) hW
  have hz0 := memC_ofBalls hcz0.1 hcz0.2
  have hw0 := memC_ofBalls hcw.1 hcw.2
  rw [← exp_I_eq] at hz0 hw0
  have := powList_getElem hw0 hz0 k hk'
  have hsk : sR g k = sR g 0 + (k : ℝ) * Δ := by
    have h0 := sR_succ g 0 k
    rwa [zero_add] at h0
  have e : Complex.exp (((2 * π * (sR g 0 * y) : ℝ) : ℂ) * I) *
      Complex.exp (((2 * π * (Δ * y) : ℝ) : ℂ) * I) ^ k = Complex.exp (((2 * π * (sR g k * y) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [hsk]; push_cast; ring
  rw [e] at this
  exact this

end SignUnc.Chk
