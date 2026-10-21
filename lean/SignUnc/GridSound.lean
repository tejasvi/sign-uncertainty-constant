import SignUnc.Ival.SoundC
import SignUnc.Calc3
import SUCert.Grid
import SignUnc.ChkSound

/-!
# Soundness of the grid evaluation (`SUCert.Grid`)

`recList` follows `e^{-πa(u - jδ)²}` (any step `δ`), `powList` follows `e^{2πi(s₀ + jΔ)y}`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex

variable {P : ℕ}

theorem recList_mem {a δ : ℝ} {rho : Ball} (hrho : mem P (Real.exp (-2 * π * a * δ ^ 2)) rho) :
    ∀ (m : ℕ) (u : ℝ) (x r : Ball), mem P (Real.exp (-π * a * u ^ 2)) x →
      mem P (Real.exp (2 * π * a * δ * u - π * a * δ ^ 2)) r →
      List.Forall₂ (fun (v : ℝ) (b : Ball) => mem P v b)
        ((List.range m).map (fun j : ℕ => Real.exp (-π * a * (u - j * δ) ^ 2))) (recList P rho m x r) := by
  intro m
  induction m with
  | zero => intro u x r _ _; simp [recList]
  | succ m ih =>
    intro u x r hx hr
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [recList]
    refine List.Forall₂.cons (by simpa using hx) ?_
    have hx' : mem P (Real.exp (-π * a * (u - δ) ^ 2)) (mul P x r) := by
      have := mem_mul hx hr
      rwa [← Real.exp_add, show -π * a * u ^ 2 + (2 * π * a * δ * u - π * a * δ ^ 2) = -π * a * (u - δ) ^ 2 by ring]
        at this
    have hr' : mem P (Real.exp (2 * π * a * δ * (u - δ) - π * a * δ ^ 2)) (mul P r rho) := by
      have := mem_mul hr hrho
      rwa [← Real.exp_add, show 2 * π * a * δ * u - π * a * δ ^ 2 + -2 * π * a * δ ^ 2 =
        2 * π * a * δ * (u - δ) - π * a * δ ^ 2 by ring] at this
    have := ih (u - δ) _ _ hx' hr'
    convert this using 2
    funext j
    simp only [Function.comp_apply, Nat.cast_succ]
    ring_nf

theorem powList_mem {w : ℂ} {W : CDisc} (hw : memC P w W) :
    ∀ (m : ℕ) (z : ℂ) (Z : CDisc), memC P z Z →
      List.Forall₂ (fun (v : ℂ) (b : CDisc) => memC P v b)
        ((List.range m).map (fun j : ℕ => z * w ^ j)) (powList P W m Z) := by
  intro m
  induction m with
  | zero => intro z Z _; simp [powList]
  | succ m ih =>
    intro z Z hz
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [powList]
    refine List.Forall₂.cons (by simpa using hz) ?_
    have := ih (z * w) _ (memC_mul hz hw)
    convert this using 2
    funext j
    simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ]
    ring


/-! ## Real semantics of a group -/

/-- The width `a` of a group. -/
noncomputable def aR (g : GGroup) : ℝ := (g.an : ℝ) / g.ad

/-- The centre `s_k = s₀ + kΔ` of a group. -/
noncomputable def sR (g : GGroup) (k : ℕ) : ℝ := (g.s0n : ℝ) / g.s0d + k * ((g.dn : ℝ) / g.dd)

/-- The step `Δ`. -/
noncomputable def dR (g : GGroup) : ℝ := (g.dn : ℝ) / g.dd

/-- A coefficient. -/
noncomputable def cR (c : ℤ × ℕ) : ℝ := (c.1 : ℝ) / c.2

/-- The pairs `(c_k, s_k)` of a group. -/
noncomputable def GGroup.csR (g : GGroup) : List (ℝ × ℝ) :=
  (List.range g.cs.length).zipWith (fun j c => (cR c, sR g j)) g.cs

/-- The triples `(a, s_k, c_k)` of a group. -/
noncomputable def GGroup.triples (g : GGroup) : List (ℝ × ℝ × ℝ) :=
  g.csR.map fun r => (aR g, r.2, r.1)

theorem sk_eq (g : GGroup) (hs : 0 < g.s0d) (hd : 0 < g.dd) (k : ℕ) :
    ((g.sk k).1 : ℝ) / ((g.sk k).2 : ℝ) = sR g k := by
  unfold GGroup.sk sR
  have h1 : (0 : ℝ) < g.s0d := by exact_mod_cast hs
  have h2 : (0 : ℝ) < g.dd := by exact_mod_cast hd
  push_cast
  field_simp

theorem sR_succ (g : GGroup) (k j : ℕ) : sR g (k + j) = sR g k + j * dR g := by
  unfold sR dR; push_cast; ring

/-- `G` holds balls for the real data of its group. -/
structure PGOk (P : ℕ) (G : PG) : Prop where
  hpos : 0 < aR G.g
  hs0d : 0 < G.g.s0d
  hdd : 0 < G.g.dd
  hA : mem P (aR G.g) G.A
  hAi : mem P (1 / aR G.g) G.Ai
  hQ : mem P (2 / Real.sqrt (aR G.g)) G.Q
  hS0 : mem P (sR G.g 0) G.S0
  hD : mem P (dR G.g) G.D
  hrho : mem P (Real.exp (-2 * π * aR G.g * dR G.g ^ 2)) G.rho
  hpa : mem P (π * aR G.g) G.pa
  hCS : List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2) G.g.csR G.CS

theorem csBalls_ok {P : ℕ} (g : GGroup) (hs : 0 < g.s0d) (hd : 0 < g.dd)
    (hc : ∀ c ∈ g.cs, 0 < c.2) :
    List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2) g.csR (csBalls P g) := by
  unfold GGroup.csR csBalls
  -- generalize the index offset
  suffices H : ∀ (L : List (ℤ × ℕ)) (i : ℕ), (∀ c ∈ L, 0 < c.2) →
      List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2)
        ((List.range' i L.length).zipWith (fun j c => (cR c, sR g j)) L)
        ((List.range' i L.length).zipWith (fun j c => (ofRat P c.1 c.2, ofRat P (g.sk j).1 (g.sk j).2)) L) by
    have := H g.cs 0 hc
    simpa [List.range_eq_range'] using this
  intro L
  induction L with
  | nil => intro i _; simp
  | cons c L ih =>
    intro i hcL
    simp only [List.length_cons, List.range'_succ, List.zipWith_cons_cons]
    refine List.Forall₂.cons ⟨?_, ?_⟩ (ih (i + 1) (fun c' hc' => hcL c' (by simp [hc'])))
    · exact mem_ofRat P c.1 c.2 (hcL c (by simp))
    · have h := mem_ofRat P (g.sk i).1 (g.sk i).2 (by unfold GGroup.sk; positivity)
      rwa [sk_eq g hs hd i] at h

theorem prepGroup_ok {P n : ℕ} {g : GGroup} {G : PG} (h : prepGroup P n g = some G) : PGOk P G := by
  unfold prepGroup at h
  split_ifs at h with hc
  obtain ⟨han, had, hs, hdn, hdd, hcs⟩ := hc
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨Q, hQ, rho, hrho, rfl⟩ := h
  have hanr : (0 : ℝ) < g.an := by exact_mod_cast han
  have hadr : (0 : ℝ) < g.ad := by exact_mod_cast had
  have hA : mem P (aR g) (ofRat P g.an g.ad) := by
    have := mem_ofRat P (g.an : ℤ) g.ad had; simpa [aR] using this
  have hD : mem P (dR g) (ofRat P g.dn g.dd) := by
    have := mem_ofRat P (g.dn : ℤ) g.dd hdd; simpa [dR] using this
  have hpa : mem P (π * aR g) (mul P (piB P) (ofRat P g.an g.ad)) := mem_mul (mem_piB P) hA
  refine ⟨div_pos hanr hadr, hs, hdd, hA, ?_, ?_, ?_, hD, ?_, hpa, ?_⟩
  · have := mem_ofRat P (g.ad : ℤ) g.an han
    have e : 1 / aR g = ((g.ad : ℤ) : ℝ) / (g.an : ℝ) := by unfold aR; push_cast; field_simp
    rw [e]; exact this
  · have := mem_twoOverSqrt had hQ; simpa [aR] using this
  · have := mem_ofRat P g.s0n g.s0d hs
    simpa [sR] using this
  · have := mem_expB' (mem_neg (mem_mul (mem_mulInt 2 hpa) (mem_mul hD hD))) hrho
    rw [show -2 * π * aR g * dR g ^ 2 = -((2 : ℤ) * (π * aR g) * (dR g * dR g)) by push_cast; ring]
    exact this
  · exact csBalls_ok g hs hdd (fun c hc' => by
      have := List.all_eq_true.mp hcs c hc'
      simpa using this)


/-! ## The lists of `gridLists` -/

theorem recList_length (rho : Ball) : ∀ (m : ℕ) (x0 r0 : Ball), (recList P rho m x0 r0).length = m
  | 0, _, _ => rfl
  | m + 1, x0, r0 => by simp [recList, recList_length rho m]

theorem powList_length (w : CDisc) : ∀ (m : ℕ) (z : CDisc), (powList P w m z).length = m
  | 0, _ => rfl
  | m + 1, z => by simp [powList, powList_length w m]

theorem recList_getElem {a δ : ℝ} {rho : Ball} (hrho : mem P (Real.exp (-2 * π * a * δ ^ 2)) rho)
    {m : ℕ} {u : ℝ} {x r : Ball} (hx : mem P (Real.exp (-π * a * u ^ 2)) x)
    (hr : mem P (Real.exp (2 * π * a * δ * u - π * a * δ ^ 2)) r) (i : ℕ) (hi : i < m) :
    mem P (Real.exp (-π * a * (u - i * δ) ^ 2)) ((recList P rho m x r)[i]'(by rw [recList_length]; exact hi)) := by
  have h := (recList_mem hrho m u x r hx hr).get (i := i) (by simpa using hi)
    (by rw [recList_length]; exact hi)
  simpa using h

theorem powList_getElem {w : ℂ} {W : CDisc} (hw : memC P w W) {m : ℕ} {z : ℂ} {Z : CDisc}
    (hz : memC P z Z) (i : ℕ) (hi : i < m) :
    memC P (z * w ^ i) ((powList P W m Z)[i]'(by rw [powList_length]; exact hi)) := by
  have h := (powList_mem hw m z Z hz).get (i := i) (by simpa using hi) (by rw [powList_length]; exact hi)
  simpa using h

theorem exp_I_eq (θ : ℝ) : Complex.exp ((θ : ℂ) * I) = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem gridLists_ok {ex : Ball → Option Ball} {cz : Ball → Option (Ball × Ball)}
    (hex : ∀ {x : ℝ} {X E : Ball}, mem P x X → ex X = some E → mem P (Real.exp x) E)
    (hcz : ∀ {u : ℝ} {U C S : Ball}, mem P u U → cz U = some (C, S) →
      mem P (Real.cos (2 * π * u)) C ∧ mem P (Real.sin (2 * π * u)) S)
    {G : PG} (hG : PGOk P G) {y : ℝ} {Y : Ball} (hY : mem P y Y)
    {Es Fs : List Ball} {Zs : List CDisc} {QH : Ball}
    (h : gridLists P ex cz G Y = some (Es, Fs, Zs, QH)) :
    (Es.length = G.g.cs.length ∧ ∀ k (hk : k < Es.length),
      mem P (Real.exp (-π * aR G.g * (y - sR G.g k) ^ 2)) Es[k]) ∧
    (Fs.length = G.g.cs.length ∧ ∀ k (hk : k < Fs.length),
      mem P (Real.exp (-π * aR G.g * (y + sR G.g k) ^ 2)) Fs[k]) ∧
    (Zs.length = G.g.cs.length ∧ ∀ k (hk : k < Zs.length),
      memC P (Complex.exp ((2 * π * (sR G.g k * y) : ℝ) * I)) Zs[k]) ∧
    mem P (2 / Real.sqrt (aR G.g) * Real.exp (-π * y ^ 2 / aR G.g)) QH := by
  unfold gridLists at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨Ek, hEk, Rup, hRup, Rdn, hRdn, F0, hF0, T0, hT0, H, hH, ⟨Z0c, Z0s⟩, hZ0, ⟨Wc, Ws⟩, hW,
    hEs, hFs, hZs, hQH⟩ := h
  set g := G.g
  set N := g.cs.length
  set ks := kStar P g Y
  set a := aR g
  set Δ := dR g
  have hks : ks ≤ N := by
    simp only [ks, kStar]; split_ifs <;> omega
  have hpi := mem_piB P
  have hu : mem P (y - sR g ks) (sub Y (ofRat P (g.sk ks).1 (g.sk ks).2)) := by
    have := mem_ofRat P (g.sk ks).1 (g.sk ks).2 (by unfold GGroup.sk; have := hG.hs0d; have := hG.hdd; positivity)
    rw [sk_eq g hG.hs0d hG.hdd ks] at this
    exact mem_sub hY this
  set u := y - sR g ks
  have hv0 : mem P (y + sR g 0) (add Y G.S0) := mem_add hY hG.hS0
  have h2paD : mem P ((2 : ℤ) * (π * a) * Δ) (mul P (mulInt 2 G.pa) G.D) := mem_mul (mem_mulInt 2 hG.hpa) hG.hD
  have hpaD2 : mem P (π * a * (Δ * Δ)) (mul P G.pa (mul P G.D G.D)) := mem_mul hG.hpa (mem_mul hG.hD hG.hD)
  have hEk' : mem P (Real.exp (-π * a * u ^ 2)) Ek := by
    have := hex (mem_neg (mem_mul hG.hpa (mem_mul hu hu))) hEk
    rwa [show -(π * a * (u * u)) = -π * a * u ^ 2 by ring] at this
  have hRup' : mem P (Real.exp (2 * π * a * Δ * u - π * a * Δ ^ 2)) Rup := by
    have := hex (mem_sub (mem_mul h2paD hu) hpaD2) hRup
    rwa [show (2 : ℤ) * (π * a) * Δ * u - π * a * (Δ * Δ) = 2 * π * a * Δ * u - π * a * Δ ^ 2 by push_cast; ring]
      at this
  have hRdn' : mem P (Real.exp (2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2)) Rdn := by
    have := hex (mem_sub (mem_neg (mem_mul h2paD hu)) hpaD2) hRdn
    rwa [show -((2 : ℤ) * (π * a) * Δ * u) - π * a * (Δ * Δ) = 2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2 by
      push_cast; ring] at this
  have hF0' : mem P (Real.exp (-π * a * (y + sR g 0) ^ 2)) F0 := by
    have := hex (mem_neg (mem_mul hG.hpa (mem_mul hv0 hv0))) hF0
    rwa [show -(π * a * ((y + sR g 0) * (y + sR g 0))) = -π * a * (y + sR g 0) ^ 2 by ring] at this
  have hT0' : mem P (Real.exp (2 * π * a * (-Δ) * (y + sR g 0) - π * a * (-Δ) ^ 2)) T0 := by
    have := hex (mem_sub (mem_neg (mem_mul h2paD hv0)) hpaD2) hT0
    rwa [show -((2 : ℤ) * (π * a) * Δ * (y + sR g 0)) - π * a * (Δ * Δ) =
      2 * π * a * (-Δ) * (y + sR g 0) - π * a * (-Δ) ^ 2 by push_cast; ring] at this
  have hrho' : mem P (Real.exp (-2 * π * a * (-Δ) ^ 2)) G.rho := by
    rw [neg_sq]; exact hG.hrho
  have hH' : mem P (Real.exp (-π * y ^ 2 / a)) H := by
    have := hex (mem_neg (mem_mul hpi (mem_mul (mem_mul hY hY) hG.hAi))) hH
    rwa [show -(π * (y * y * (1 / a))) = -π * y ^ 2 / a by ring] at this
  -- the down list starts one step below `ks`
  have hx1 : mem P (Real.exp (-π * a * (u - (-Δ)) ^ 2)) (mul P Ek Rdn) := by
    have := mem_mul hEk' hRdn'
    rwa [← Real.exp_add, show -π * a * u ^ 2 + (2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2) =
      -π * a * (u - (-Δ)) ^ 2 by ring] at this
  have hr1 : mem P (Real.exp (2 * π * a * (-Δ) * (u - (-Δ)) - π * a * (-Δ) ^ 2)) (mul P Rdn G.rho) := by
    have := mem_mul hRdn' hrho'
    rwa [← Real.exp_add, show 2 * π * a * (-Δ) * u - π * a * (-Δ) ^ 2 + -2 * π * a * (-Δ) ^ 2 =
      2 * π * a * (-Δ) * (u - (-Δ)) - π * a * (-Δ) ^ 2 by ring] at this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [← hEs]; simp [recList_length]; omega
  · intro k hk
    subst hEs
    have hlen1 : (recList P G.rho ks (mul P Ek Rdn) (mul P Rdn G.rho)).reverse.length = ks := by
      simp [recList_length]
    by_cases hlt : k < ks
    · rw [List.getElem_append_left (by rw [hlen1]; exact hlt), List.getElem_reverse]
      have hj : ks - 1 - k < ks := by omega
      have := recList_getElem hrho' hx1 hr1 (ks - 1 - k) hj
      have hsk : sR g ks = sR g k + (((ks - 1 - k : ℕ) : ℝ) + 1) * Δ := by
        have h0 := sR_succ g k (ks - 1 - k + 1)
        rw [show k + (ks - 1 - k + 1) = ks by omega] at h0
        rw [h0]; push_cast; ring
      have e : u - -Δ - ((ks - 1 - k : ℕ) : ℝ) * -Δ = y - sR g k := by
        simp only [u]; rw [hsk]; ring
      rw [e] at this
      simpa [recList_length] using this
    · rw [List.getElem_append_right (by rw [hlen1]; omega)]
      have hk2 : k < ks + (N - ks) := by
        have := hk; simp [recList_length] at this; omega
      have hj : k - ks < N - ks := by omega
      have := recList_getElem hG.hrho hEk' hRup' (k - ks) hj
      have hsk : sR g k = sR g ks + ((k - ks : ℕ) : ℝ) * Δ := by
        have h0 := sR_succ g ks (k - ks)
        rw [show ks + (k - ks) = k by omega] at h0
        exact h0
      have e : u - ((k - ks : ℕ) : ℝ) * Δ = y - sR g k := by
        simp only [u]; rw [hsk]; ring
      rw [e] at this
      simpa [hlen1] using this
  · rw [← hFs, recList_length]
  · intro k hk
    subst hFs
    have hk' : k < N := by simpa [recList_length] using hk
    have := recList_getElem hrho' hF0' hT0' k hk'
    have hsk : sR g k = sR g 0 + (k : ℝ) * Δ := by
      have h0 := sR_succ g 0 k
      rwa [zero_add] at h0
    have e : y + sR g 0 - (k : ℝ) * -Δ = y + sR g k := by rw [hsk]; ring
    rw [e] at this
    exact this
  · rw [← hZs, powList_length]
  · intro k hk
    subst hZs
    have hk' : k < N := by simpa [powList_length] using hk
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
  · subst hQH; exact mem_mul hG.hQ hH'


/-! ## One centre: `row012` and `row3` -/

section rows

variable {G : PG} {y c sv : ℝ} {Y QH C Sb E Fm : Ball} {Z : CDisc}

theorem row_inputs (hZ : memC P (Complex.exp ((2 * π * (sv * y) : ℝ) * I)) Z) :
    mem P (Real.cos (2 * π * sv * y)) Z.re ∧ mem P (Real.sin (2 * π * sv * y)) Z.im := by
  have h1 := mem_re hZ
  have h2 := mem_im hZ
  rw [Complex.exp_ofReal_mul_I_re] at h1
  rw [Complex.exp_ofReal_mul_I_im] at h2
  rw [show 2 * π * sv * y = 2 * π * (sv * y) by ring]
  exact ⟨h1, h2⟩

theorem mem_row012 (hG : PGOk P G) (hY : mem P y Y)
    (hQH : mem P (2 / Real.sqrt (aR G.g) * Real.exp (-π * y ^ 2 / aR G.g)) QH)
    (hC : mem P c C) (hS : mem P sv Sb)
    (hE : mem P (Real.exp (-π * aR G.g * (y - sv) ^ 2)) E) (hF : mem P (Real.exp (-π * aR G.g * (y + sv) ^ 2)) Fm)
    (hZ : memC P (Complex.exp ((2 * π * (sv * y) : ℝ) * I)) Z) :
    mem P (c * (gb (aR G.g) sv y + gbh (aR G.g) sv y)) (row012 P G Y QH C Sb E Fm Z).1 ∧
    mem P (c * (gb1 (aR G.g) sv y + gbh1 (aR G.g) sv y)) (row012 P G Y QH C Sb E Fm Z).2.1 ∧
    mem P (c * (gb2 (aR G.g) sv y + gbh2 (aR G.g) sv y)) (row012 P G Y QH C Sb E Fm Z).2.2 := by
  obtain ⟨hCs, hSn⟩ := row_inputs hZ
  set a := aR G.g
  have hpi := mem_piB P
  have hd1 : mem P (y - sv) (sub Y Sb) := mem_sub hY hS
  have hd2 : mem P (y + sv) (add Y Sb) := mem_add hY hS
  have hpiy : mem P (π * (y * (1 / a))) (mul P (piB P) (mul P Y G.Ai)) := mem_mul hpi (mem_mul hY hG.hAi)
  have hpia : mem P (π * (1 / a)) (mul P (piB P) G.Ai) := mem_mul hpi hG.hAi
  have hpis : mem P (π * sv) (mul P (piB P) Sb) := mem_mul hpi hS
  have hpa2 := mem_mul hG.hpa hG.hpa
  refine ⟨?_, ?_, ?_⟩
  · have := mem_mul hC (mem_add (mem_add hE hF) (mem_mul hQH hCs))
    have e : c * (gb a sv y + gbh a sv y) = c * (Real.exp (-π * a * (y - sv) ^ 2) + Real.exp (-π * a * (y + sv) ^ 2)
        + 2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * Real.cos (2 * π * sv * y)) := by
      unfold gb gbh; ring
    rw [e]; exact this
  · have hgb1 := mem_neg (mem_mul (mem_mulInt 2 hG.hpa) (mem_add (mem_mul hd1 hE) (mem_mul hd2 hF)))
    have hgbh1 := mem_mul hQH (mem_sub (mem_neg (mem_mul (mem_mulInt 2 hpiy) hCs)) (mem_mul (mem_mulInt 2 hpis) hSn))
    have := mem_mul hC (mem_add hgb1 hgbh1)
    have e : c * (gb1 a sv y + gbh1 a sv y) = c * (-((2 : ℤ) * (π * a) * ((y - sv) * Real.exp (-π * a * (y - sv) ^ 2) +
        (y + sv) * Real.exp (-π * a * (y + sv) ^ 2))) +
        2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * (-((2 : ℤ) * (π * (y * (1 / a))) * Real.cos (2 * π * sv * y)) -
          (2 : ℤ) * (π * sv) * Real.sin (2 * π * sv * y))) := by
      unfold gb1 gbh1; push_cast; ring
    rw [e]; exact this
  · have hc1 := mem_sub (mem_mulInt 4 (mem_mul hpa2 (mem_mul hd1 hd1))) (mem_mulInt 2 hG.hpa)
    have hc2 := mem_sub (mem_mulInt 4 (mem_mul hpa2 (mem_mul hd2 hd2))) (mem_mulInt 2 hG.hpa)
    have hk1 := mem_sub (mem_sub (mem_mulInt 4 (mem_mul hpiy hpiy)) (mem_mulInt 2 hpia)) (mem_mulInt 4 (mem_mul hpis hpis))
    have hk2 := mem_mulInt 8 (mem_mul hpis hpiy)
    have := mem_mul hC (mem_add (mem_add (mem_mul hc1 hE) (mem_mul hc2 hF))
      (mem_mul hQH (mem_add (mem_mul hk1 hCs) (mem_mul hk2 hSn))))
    have e : c * (gb2 a sv y + gbh2 a sv y) = c * (
        (((4 : ℤ) * (π * a * (π * a) * ((y - sv) * (y - sv))) - (2 : ℤ) * (π * a)) * Real.exp (-π * a * (y - sv) ^ 2) +
         ((4 : ℤ) * (π * a * (π * a) * ((y + sv) * (y + sv))) - (2 : ℤ) * (π * a)) * Real.exp (-π * a * (y + sv) ^ 2)) +
        2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
          ((((4 : ℤ) * (π * (y * (1 / a)) * (π * (y * (1 / a)))) - (2 : ℤ) * (π * (1 / a))) -
              (4 : ℤ) * (π * sv * (π * sv))) * Real.cos (2 * π * sv * y) +
            (8 : ℤ) * (π * sv * (π * (y * (1 / a)))) * Real.sin (2 * π * sv * y))) := by
      unfold gb2 gbh2; push_cast; ring
    rw [e]; exact this

theorem mem_row3 (hG : PGOk P G) (hY : mem P y Y)
    (hQH : mem P (2 / Real.sqrt (aR G.g) * Real.exp (-π * y ^ 2 / aR G.g)) QH)
    (hC : mem P c C) (hS : mem P sv Sb)
    (hE : mem P (Real.exp (-π * aR G.g * (y - sv) ^ 2)) E) (hF : mem P (Real.exp (-π * aR G.g * (y + sv) ^ 2)) Fm)
    (hZ : memC P (Complex.exp ((2 * π * (sv * y) : ℝ) * I)) Z) :
    mem P (c * (gb3 (aR G.g) sv y + gbh3 (aR G.g) sv y)) (row3 P G Y QH C Sb E Fm Z) := by
  obtain ⟨hCs, hSn⟩ := row_inputs hZ
  set a := aR G.g
  have hpi := mem_piB P
  have hd1 : mem P (y - sv) (sub Y Sb) := mem_sub hY hS
  have hd2 : mem P (y + sv) (add Y Sb) := mem_add hY hS
  have hpiy : mem P (π * (y * (1 / a))) (mul P (piB P) (mul P Y G.Ai)) := mem_mul hpi (mem_mul hY hG.hAi)
  have hpia : mem P (π * (1 / a)) (mul P (piB P) G.Ai) := mem_mul hpi hG.hAi
  have hpis : mem P (π * sv) (mul P (piB P) Sb) := mem_mul hpi hS
  have hpa2 := mem_mul hG.hpa hG.hpa
  have hpa3 := mem_mul hpa2 hG.hpa
  have he1 := mem_sub (mem_mulInt 12 (mem_mul hpa2 hd1)) (mem_mulInt 8 (mem_mul hpa3 (mem_mul hd1 (mem_mul hd1 hd1))))
  have he2 := mem_sub (mem_mulInt 12 (mem_mul hpa2 hd2)) (mem_mulInt 8 (mem_mul hpa3 (mem_mul hd2 (mem_mul hd2 hd2))))
  have hk1 := mem_sub (mem_sub (mem_mulInt 4 (mem_mul hpiy hpiy)) (mem_mulInt 2 hpia)) (mem_mulInt 4 (mem_mul hpis hpis))
  have hk2 := mem_mulInt 8 (mem_mul hpis hpiy)
  have hl1 := mem_add (mem_add (mem_neg (mem_mul (mem_mulInt 2 hpiy) hk1)) (mem_mulInt 8 (mem_mul hpia hpiy)))
    (mem_mul (mem_mulInt 2 hpis) hk2)
  have hl2 := mem_add (mem_sub (mem_neg (mem_mul (mem_mulInt 2 hpiy) hk2)) (mem_mul (mem_mulInt 2 hpis) hk1))
    (mem_mulInt 8 (mem_mul hpis hpia))
  have := mem_mul hC (mem_add (mem_add (mem_mul he1 hE) (mem_mul he2 hF))
    (mem_mul hQH (mem_add (mem_mul hl1 hCs) (mem_mul hl2 hSn))))
  have e : c * (gb3 a sv y + gbh3 a sv y) = c * (
      (((12 : ℤ) * (π * a * (π * a) * (y - sv)) - (8 : ℤ) * (π * a * (π * a) * (π * a) * ((y - sv) * ((y - sv) * (y - sv)))))
          * Real.exp (-π * a * (y - sv) ^ 2) +
        ((12 : ℤ) * (π * a * (π * a) * (y + sv)) - (8 : ℤ) * (π * a * (π * a) * (π * a) * ((y + sv) * ((y + sv) * (y + sv)))))
          * Real.exp (-π * a * (y + sv) ^ 2)) +
      2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
        ((-((2 : ℤ) * (π * (y * (1 / a))) * (((4 : ℤ) * (π * (y * (1 / a)) * (π * (y * (1 / a)))) - (2 : ℤ) * (π * (1 / a))) -
            (4 : ℤ) * (π * sv * (π * sv)))) + (8 : ℤ) * (π * (1 / a) * (π * (y * (1 / a)))) +
            (2 : ℤ) * (π * sv) * ((8 : ℤ) * (π * sv * (π * (y * (1 / a)))))) * Real.cos (2 * π * sv * y) +
          (-((2 : ℤ) * (π * (y * (1 / a))) * ((8 : ℤ) * (π * sv * (π * (y * (1 / a)))))) -
            (2 : ℤ) * (π * sv) * (((4 : ℤ) * (π * (y * (1 / a)) * (π * (y * (1 / a)))) - (2 : ℤ) * (π * (1 / a))) -
              (4 : ℤ) * (π * sv * (π * sv))) + (8 : ℤ) * (π * sv * (π * (1 / a)))) * Real.sin (2 * π * sv * y))) := by
    unfold gb3 gbh3; push_cast; ring
  rw [e]; exact this

end rows


/-! ## Sums over a group -/

theorem gsum3_cons (q : ℝ × ℝ × ℝ) (L : List (ℝ × ℝ × ℝ)) (x : ℝ) :
    gsum3 (q :: L) x = q.2.2 * (gb3 q.1 q.2.1 x + gbh3 q.1 q.2.1 x) + gsum3 L x := by
  obtain ⟨a, s, c⟩ := q; rfl

theorem mem_fold012 {G : PG} {y : ℝ} {Y QH : Ball} (hG : PGOk P G) (hY : mem P y Y)
    (hQH : mem P (2 / Real.sqrt (aR G.g) * Real.exp (-π * y ^ 2 / aR G.g)) QH) :
    ∀ (rr : List (ℝ × ℝ)) (cs : List (Ball × Ball)) (es fs : List Ball) (zs : List CDisc),
      List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2) rr cs →
      List.Forall₂ (fun (r : ℝ × ℝ) (e : Ball) => mem P (Real.exp (-π * aR G.g * (y - r.2) ^ 2)) e) rr es →
      List.Forall₂ (fun (r : ℝ × ℝ) (f : Ball) => mem P (Real.exp (-π * aR G.g * (y + r.2) ^ 2)) f) rr fs →
      List.Forall₂ (fun (r : ℝ × ℝ) (z : CDisc) => memC P (Complex.exp ((2 * π * (r.2 * y) : ℝ) * I)) z) rr zs →
      mem P (gsum (rr.map fun r => (aR G.g, r.2, r.1)) y) (fold012 P G Y QH cs es fs zs).1 ∧
      mem P (gsum1 (rr.map fun r => (aR G.g, r.2, r.1)) y) (fold012 P G Y QH cs es fs zs).2.1 ∧
      mem P (gsum2 (rr.map fun r => (aR G.g, r.2, r.1)) y) (fold012 P G Y QH cs es fs zs).2.2 := by
  intro rr
  induction rr with
  | nil =>
    intro cs es fs zs hc he hf hz
    cases hc; cases he; cases hf; cases hz
    simp [fold012, gsum, gsum1, gsum2, mem]
  | cons r rr ih =>
    intro cs es fs zs hc he hf hz
    cases hc with
    | cons hc0 hc1 =>
    cases he with
    | cons he0 he1 =>
    cases hf with
    | cons hf0 hf1 =>
    cases hz with
    | cons hz0 hz1 =>
    rename_i b cs' e es' f fs' z zs'
    obtain ⟨C, Sb⟩ := b
    have hrow := mem_row012 hG hY hQH hc0.1 hc0.2 he0 hf0 hz0
    have hrest := ih cs' es' fs' zs' hc1 he1 hf1 hz1
    simp only [fold012, add3, List.map_cons, gsum_cons, gsum1_cons, gsum2_cons]
    exact ⟨mem_add hrow.1 hrest.1, mem_add hrow.2.1 hrest.2.1, mem_add hrow.2.2 hrest.2.2⟩

theorem mem_fold3 {G : PG} {y : ℝ} {Y QH : Ball} (hG : PGOk P G) (hY : mem P y Y)
    (hQH : mem P (2 / Real.sqrt (aR G.g) * Real.exp (-π * y ^ 2 / aR G.g)) QH) :
    ∀ (rr : List (ℝ × ℝ)) (cs : List (Ball × Ball)) (es fs : List Ball) (zs : List CDisc),
      List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2) rr cs →
      List.Forall₂ (fun (r : ℝ × ℝ) (e : Ball) => mem P (Real.exp (-π * aR G.g * (y - r.2) ^ 2)) e) rr es →
      List.Forall₂ (fun (r : ℝ × ℝ) (f : Ball) => mem P (Real.exp (-π * aR G.g * (y + r.2) ^ 2)) f) rr fs →
      List.Forall₂ (fun (r : ℝ × ℝ) (z : CDisc) => memC P (Complex.exp ((2 * π * (r.2 * y) : ℝ) * I)) z) rr zs →
      mem P (gsum3 (rr.map fun r => (aR G.g, r.2, r.1)) y) (fold3 P G Y QH cs es fs zs) := by
  intro rr
  induction rr with
  | nil =>
    intro cs es fs zs hc he hf hz
    cases hc; cases he; cases hf; cases hz
    simp [fold3, gsum3, mem]
  | cons r rr ih =>
    intro cs es fs zs hc he hf hz
    cases hc with
    | cons hc0 hc1 =>
    cases he with
    | cons he0 he1 =>
    cases hf with
    | cons hf0 hf1 =>
    cases hz with
    | cons hz0 hz1 =>
    rename_i b cs' e es' f fs' z zs'
    obtain ⟨C, Sb⟩ := b
    have hrow := mem_row3 hG hY hQH hc0.1 hc0.2 he0 hf0 hz0
    have hrest := ih cs' es' fs' zs' hc1 he1 hf1 hz1
    simp only [fold3, List.map_cons, gsum3_cons]
    exact mem_add hrow hrest

theorem csR_length (g : GGroup) : g.csR.length = g.cs.length := by
  simp [GGroup.csR]

theorem csR_getElem_snd (g : GGroup) (k : ℕ) (hk : k < g.csR.length) : (g.csR[k]).2 = sR g k := by
  simp [GGroup.csR]

/-- From the index facts of `gridLists_ok` to relations along `csR`. -/
theorem forall₂_csR {α : Type*} (g : GGroup) (l : List α) (R : ℝ → α → Prop)
    (hlen : l.length = g.cs.length) (h : ∀ k (hk : k < l.length), R (sR g k) l[k]) :
    List.Forall₂ (fun (r : ℝ × ℝ) (x : α) => R r.2 x) g.csR l := by
  apply List.forall₂_of_length_eq_of_get (by rw [csR_length, hlen])
  intro i h1 h2
  simp only [List.get_eq_getElem]
  rw [csR_getElem_snd g i h1]
  exact h i h2

theorem mem_group012 {n k : ℕ} {G : PG} (hG : PGOk P G) {y : ℝ} {Y : Ball} (hY : mem P y Y)
    {G0 G1 G2 : Ball} (h : group012 P n k G Y = some (G0, G1, G2)) :
    mem P (gsum G.g.triples y) G0 ∧ mem P (gsum1 G.g.triples y) G1 ∧ mem P (gsum2 G.g.triples y) G2 := by
  unfold group012 at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨⟨Es, Fs, Zs, QH⟩, hL, hfold⟩ := h
  obtain ⟨⟨hEl, hE⟩, ⟨hFl, hF⟩, ⟨hZl, hZ⟩, hQH⟩ :=
    gridLists_ok (fun hx hX => mem_expB' hx hX) (fun hu hU => mem_cosSinTurn hu hU) hG hY hL
  have := mem_fold012 hG hY hQH G.g.csR G.CS Es Fs Zs hG.hCS
    (forall₂_csR G.g Es (fun sv e => mem P (Real.exp (-π * aR G.g * (y - sv) ^ 2)) e) hEl hE)
    (forall₂_csR G.g Fs (fun sv f => mem P (Real.exp (-π * aR G.g * (y + sv) ^ 2)) f) hFl hF)
    (forall₂_csR G.g Zs (fun sv z => memC P (Complex.exp ((2 * π * (sv * y) : ℝ) * I)) z) hZl hZ)
  rw [hfold] at this
  exact this

theorem mem_group3 {n k : ℕ} {G : PG} (hG : PGOk P G) {y : ℝ} {Y : Ball} (hY : mem P y Y)
    {G3 : Ball} (h : group3 P n k G Y = some G3) : mem P (gsum3 G.g.triples y) G3 := by
  unfold group3 at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨⟨Es, Fs, Zs, QH⟩, hL, hfold⟩ := h
  obtain ⟨⟨hEl, hE⟩, ⟨hFl, hF⟩, ⟨hZl, hZ⟩, hQH⟩ :=
    gridLists_ok (fun hx hX => mem_expH hx hX) (fun hu hU => mem_cosSinTurnC hu hU) hG hY hL
  have := mem_fold3 hG hY hQH G.g.csR G.CS Es Fs Zs hG.hCS
    (forall₂_csR G.g Es (fun sv e => mem P (Real.exp (-π * aR G.g * (y - sv) ^ 2)) e) hEl hE)
    (forall₂_csR G.g Fs (fun sv f => mem P (Real.exp (-π * aR G.g * (y + sv) ^ 2)) f) hFl hF)
    (forall₂_csR G.g Zs (fun sv z => memC P (Complex.exp ((2 * π * (sv * y) : ℝ) * I)) z) hZl hZ)
  rw [hfold] at this
  exact this


/-! ## Lists of groups -/

theorem gsum_append (L1 L2 : List (ℝ × ℝ × ℝ)) (x : ℝ) : gsum (L1 ++ L2) x = gsum L1 x + gsum L2 x := by
  induction L1 with
  | nil => simp [gsum]
  | cons q L ih => rw [List.cons_append, gsum_cons, gsum_cons, ih]; ring

theorem gsum1_append (L1 L2 : List (ℝ × ℝ × ℝ)) (x : ℝ) : gsum1 (L1 ++ L2) x = gsum1 L1 x + gsum1 L2 x := by
  induction L1 with
  | nil => simp [gsum1]
  | cons q L ih => rw [List.cons_append, gsum1_cons, gsum1_cons, ih]; ring

theorem gsum2_append (L1 L2 : List (ℝ × ℝ × ℝ)) (x : ℝ) : gsum2 (L1 ++ L2) x = gsum2 L1 x + gsum2 L2 x := by
  induction L1 with
  | nil => simp [gsum2]
  | cons q L ih => rw [List.cons_append, gsum2_cons, gsum2_cons, ih]; ring

theorem gsum3_append (L1 L2 : List (ℝ × ℝ × ℝ)) (x : ℝ) : gsum3 (L1 ++ L2) x = gsum3 L1 x + gsum3 L2 x := by
  induction L1 with
  | nil => simp [gsum3]
  | cons q L ih => rw [List.cons_append, gsum3_cons, gsum3_cons, ih]; ring

/-- The triples of a list of groups. -/
noncomputable def gsTriples : List PG → List (ℝ × ℝ × ℝ)
  | [] => []
  | G :: Gs => G.g.triples ++ gsTriples Gs

theorem mem_groups012 {n k : ℕ} {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ {gs : List PG}, (∀ G ∈ gs, PGOk P G) → ∀ {G0 G1 G2 : Ball}, groups012 P n k Y gs = some (G0, G1, G2) →
      mem P (gsum (gsTriples gs) y) G0 ∧ mem P (gsum1 (gsTriples gs) y) G1 ∧ mem P (gsum2 (gsTriples gs) y) G2
  | [], _, G0, G1, G2, h => by
    simp only [groups012, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [gsTriples, gsum, gsum1, gsum2, mem]
  | G :: gs, hok, G0, G1, G2, h => by
    simp only [groups012, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨a0, a1, a2⟩, ha, ⟨b0, b1, b2⟩, hb, hab⟩ := h
    simp only [add3, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl, rfl⟩ := hab
    have h1 := mem_group012 (hok G (by simp)) hY ha
    have h2 := mem_groups012 hY (fun G' hG' => hok G' (by simp [hG'])) hb
    simp only [gsTriples, gsum_append, gsum1_append, gsum2_append]
    exact ⟨mem_add h1.1 h2.1, mem_add h1.2.1 h2.2.1, mem_add h1.2.2 h2.2.2⟩

theorem mem_groups3 {n k : ℕ} {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ {gs : List PG}, (∀ G ∈ gs, PGOk P G) → ∀ {G3 : Ball}, groups3 P n k Y gs = some G3 →
      mem P (gsum3 (gsTriples gs) y) G3
  | [], _, G3, h => by
    simp only [groups3, Option.some.injEq] at h
    subst h
    simp [gsTriples, gsum3, mem]
  | G :: gs, hok, G3, h => by
    simp only [groups3, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [gsTriples, gsum3_append]
    exact mem_add (mem_group3 (hok G (by simp)) hY ha) (mem_groups3 hY (fun G' hG' => hok G' (by simp [hG'])) hb)

theorem gsTriples_pos : ∀ {gs : List PG}, (∀ G ∈ gs, PGOk P G) → ∀ q ∈ gsTriples gs, 0 < q.1
  | [], _ => by simp [gsTriples]
  | G :: gs, hok => by
    intro q hq
    simp only [gsTriples, List.mem_append] at hq
    rcases hq with hq | hq
    · simp only [GGroup.triples, List.mem_map] at hq
      obtain ⟨r, _, rfl⟩ := hq
      exact (hok G (by simp)).hpos
    · exact gsTriples_pos (fun G' hG' => hok G' (by simp [hG'])) q hq

theorem prepGroups_ok {n : ℕ} : ∀ {L : List GGroup} {gs : List PG}, prepGroups P n L = some gs → ∀ G ∈ gs, PGOk P G
  | [], gs, h => by simp [prepGroups] at h; subst h; simp
  | g :: L, gs, h => by
    simp only [prepGroups, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨G, hG, Gs, hGs, rfl⟩ := h
    intro G' hG'
    simp only [List.mem_cons] at hG'
    rcases hG' with rfl | hG'
    · exact prepGroup_ok hG
    · exact prepGroups_ok hGs G' hG'


/-! ## The third-order tests -/

/-- Minimum of `α - β x + γ x²/2` over `x ≥ 0` for `γ > 0`. -/
theorem quad_min {α β γ x : ℝ} (hγ : 0 < γ) (hpos : β ^ 2 < 2 * γ * α) : 0 < α - β * x + γ * x ^ 2 / 2 := by
  have key : 2 * γ * (α - β * x + γ * x ^ 2 / 2) = (γ * x - β) ^ 2 + (2 * γ * α - β ^ 2) := by ring
  have : 0 < 2 * γ * (α - β * x + γ * x ^ 2 / 2) := by rw [key]; nlinarith [sq_nonneg (γ * x - β)]
  nlinarith

/-- `(c · (K/c)) = K`-type scaling of a minimum with `0`. -/
theorem min_scale {K c : ℝ} (hc : 0 < c) : c * min (K / c) 0 = min K 0 := by
  rw [mul_min_of_nonneg _ _ hc.le, mul_zero, mul_div_cancel₀ _ hc.ne']

theorem ivOKg_sound {n k : ℕ} {gs : List PG} (hok : ∀ G ∈ gs, PGOk P G) {lo hi : ℤ}
    (h : ivOKg P n k gs lo hi = true) :
    ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) ((hi : ℝ) / 2 ^ P), 0 < gsum (gsTriples gs) y := by
  intro y hy
  have hP := two_pow_pos' P
  set D : ℝ := (2 : ℝ) ^ P with hD
  have hlohi : (lo : ℝ) ≤ hi := by
    have := hy.1.trans hy.2
    rwa [div_le_div_iff_of_pos_right hP] at this
  have hlohi' : lo ≤ hi := by exact_mod_cast hlohi
  unfold ivOKg at h
  simp only at h
  set y0 : ℤ := (lo + hi) / 2 with hy0
  set η : ℕ := (max (y0 - lo) (hi - y0)).toNat with hη
  set L := gsTriples gs
  have hL := gsTriples_pos hok
  have hf := hasDerivAt_gsum L
  have hf1 := hasDerivAt_gsum1 L hL
  have hf2 := hasDerivAt_gsum2 L hL
  have hmax : max (y0 - lo) (hi - y0) ≤ (η : ℤ) := Int.self_le_toNat _
  have h1r : ((y0 : ℝ) - lo) ≤ η := by exact_mod_cast (le_max_left _ _).trans hmax
  have h2r : ((hi : ℝ) - y0) ≤ η := by exact_mod_cast (le_max_right _ _).trans hmax
  set e : ℝ := (η : ℝ) / D with he
  set c0 : ℝ := (y0 : ℝ) / D with hc0
  have he0 : 0 ≤ e := by positivity
  have hloc : (lo : ℝ) / D ≥ c0 - e := by
    rw [hc0, he, ← sub_div, ge_iff_le, div_le_div_iff_of_pos_right hP]; linarith
  have hhic : (hi : ℝ) / D ≤ c0 + e := by
    rw [hc0, he, ← add_div, div_le_div_iff_of_pos_right hP]; linarith
  cases h3 : groups3 P n k ⟨y0, η⟩ gs with
  | none => simp [h3] at h
  | some G3 =>
    set M : ℝ := (G3.absHi : ℝ) / D with hMdef
    have hM : ∀ x ∈ Set.Icc (c0 - e) (c0 + e), |gsum3 L x| ≤ M := by
      intro x hx
      have hxm : mem P x (⟨y0, η⟩ : Ball) := by
        apply mem_center
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      exact abs_le_absHi (mem_groups3 hxm hok h3)
    have hM0 : 0 ≤ M := by positivity
    simp only [h3, Bool.or_eq_true] at h
    rcases h with hc | hl
    · -- centred tests
      cases h01 : groups012 P n k ⟨y0, 0⟩ gs with
      | none => simp [h01] at hc
      | some G012 =>
        obtain ⟨G0, G1, G2⟩ := G012
        simp only [h01, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hg0, hg1, hg2⟩ := mem_groups012 (mem_point P y0) hok h01
        have hyI : y ∈ Set.Icc (c0 - e) (c0 + e) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have hT := taylor3_lower hf hf1 hf2 he0 hM y hyI
        set t := y - c0 with ht
        have hte : |t| ≤ e := abs_le.mpr ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
        set A : ℝ := (G0.m : ℝ) - G0.r with hAdef
        set B : ℝ := (G1.absHi : ℝ) with hBdef
        set C2 : ℝ := (G2.m : ℝ) - G2.r with hC2def
        set K : ℝ := 3 * C2 * D - (G3.absHi : ℝ) * η with hKdef
        have hA : A / D ≤ gsum L c0 := by
          unfold mem at hg0
          have := (abs_le.mp hg0).1
          rw [hAdef, sub_div]; linarith
        have hB : |gsum1 L c0| ≤ B / D := abs_le_absHi hg1
        have hC : C2 / D ≤ gsum2 L c0 := by
          unfold mem at hg2
          have := (abs_le.mp hg2).1
          rw [hC2def, sub_div]; linarith
        set κl : ℝ := K / (3 * D ^ 2) with hκl
        have hκ : κl ≤ gsum2 L c0 - M * e / 3 := by
          have e1 : κl = C2 / D - M * e / 3 := by
            rw [hκl, hKdef, hMdef, he]; field_simp <;> ring
          rw [e1]; linarith
        have hlin : -(B / D * |t|) ≤ gsum1 L c0 * t := by
          have h1 := neg_abs_le (gsum1 L c0 * t)
          rw [abs_mul] at h1
          have h2 : |gsum1 L c0| * |t| ≤ B / D * |t| := mul_le_mul_of_nonneg_right hB (abs_nonneg t)
          linarith
        rcases hc with ⟨hK, hQ⟩ | hb
        · -- convex case
          have hKr : (0 : ℝ) < K := by
            have : ((0 : ℤ) : ℝ) < ((3 * (G2.m - (G2.r : ℤ)) * ((2 ^ P : ℕ) : ℤ) - ((G3.absHi : ℕ) : ℤ) * (η : ℤ) : ℤ) : ℝ) := by
              exact_mod_cast hK
            push_cast at this
            rw [← hD, ← hC2def, ← hKdef] at this
            exact this
          have hQr : 3 * B * B * D < 2 * K * A := by
            have : ((3 * ((G1.absHi : ℕ) : ℤ) * ((G1.absHi : ℕ) : ℤ) * ((2 ^ P : ℕ) : ℤ) : ℤ) : ℝ) <
                ((2 * (3 * (G2.m - (G2.r : ℤ)) * ((2 ^ P : ℕ) : ℤ) - ((G3.absHi : ℕ) : ℤ) * (η : ℤ)) *
                  (G0.m - (G0.r : ℤ)) : ℤ) : ℝ) := by exact_mod_cast hQ
            push_cast at this
            rw [← hD, ← hAdef, ← hBdef, ← hC2def, ← hKdef] at this
            exact this
          have hKpos : 0 < κl := by rw [hκl]; positivity
          have hq := quad_min (α := A / D) (β := B / D) (x := |t|) hKpos (by
            have e1 : 2 * κl * (A / D) - (B / D) ^ 2 = (2 * K * A - 3 * B * B * D) / (3 * D ^ 3) := by
              rw [hκl]; field_simp <;> ring
            have : 0 < 2 * κl * (A / D) - (B / D) ^ 2 := by
              rw [e1]; exact div_pos (by linarith) (by positivity)
            linarith)
          have hsq : κl * |t| ^ 2 / 2 ≤ (gsum2 L c0 - M * e / 3) * t ^ 2 / 2 := by
            rw [sq_abs]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hκ (sq_nonneg t)) (by norm_num)
          have hlin2 : -(B / D * |t|) ≤ gsum1 L c0 * t := hlin
          linarith
        · -- general case
          have hbr : (0 : ℝ) < 6 * A * D ^ 3 - 6 * B * η * D ^ 2 + min K 0 * η ^ 2 := by
            have : ((0 : ℤ) : ℝ) < ((6 * (G0.m - (G0.r : ℤ)) * ((2 ^ P : ℕ) : ℤ) * ((2 ^ P : ℕ) : ℤ) *
                ((2 ^ P : ℕ) : ℤ) - 6 * ((G1.absHi : ℕ) : ℤ) * (η : ℤ) * ((2 ^ P : ℕ) : ℤ) * ((2 ^ P : ℕ) : ℤ) +
                min (3 * (G2.m - (G2.r : ℤ)) * ((2 ^ P : ℕ) : ℤ) - ((G3.absHi : ℕ) : ℤ) * (η : ℤ)) 0 * (η : ℤ) *
                (η : ℤ) : ℤ) : ℝ) := by exact_mod_cast hb
            push_cast at this
            rw [← hD, ← hAdef, ← hBdef, ← hC2def, ← hKdef] at this
            have e2 : 6 * A * D ^ 3 - 6 * B * η * D ^ 2 + min K 0 * η ^ 2 =
                6 * A * D * D * D - 6 * B * η * D * D + min K 0 * η * η := by ring
            rw [e2]; exact this
          have hmin : 3 * D ^ 2 * min κl 0 = min K 0 := by rw [hκl]; exact min_scale (by positivity)
          have hval : 0 < A / D - B / D * e + min κl 0 * e ^ 2 / 2 := by
            have e1 : A / D - B / D * e + min κl 0 * e ^ 2 / 2 =
                (6 * A * D ^ 3 - 6 * B * η * D ^ 2 + (3 * D ^ 2 * min κl 0) * η ^ 2) / (6 * D ^ 4) := by
              rw [he]; field_simp <;> ring
            rw [e1, hmin]; exact div_pos hbr (by positivity)
          have hmin2 : min κl 0 * e ^ 2 ≤ min κl 0 * t ^ 2 := by
            have h1 : t ^ 2 ≤ e ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hte 2
            have hm : min κl 0 ≤ 0 := min_le_right _ _
            exact mul_le_mul_of_nonpos_left h1 hm
          have hq2 : min κl 0 * t ^ 2 / 2 ≤ (gsum2 L c0 - M * e / 3) * t ^ 2 / 2 := by
            have h1 : min κl 0 ≤ gsum2 L c0 - M * e / 3 := (min_le_left _ _).trans hκ
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (sq_nonneg t)) (by norm_num)
          have hlin2 : B / D * |t| ≤ B / D * e := mul_le_mul_of_nonneg_left hte (by positivity)
          linarith
    · -- left-anchored test
      cases h01 : groups012 P n k ⟨lo, 0⟩ gs with
      | none => simp [h01] at hl
      | some G012 =>
        obtain ⟨G0, G1, G2⟩ := G012
        simp only [h01, Bool.and_eq_true, decide_eq_true_eq] at hl
        obtain ⟨hA0, hQ⟩ := hl
        obtain ⟨hg0, hg1, hg2⟩ := mem_groups012 (mem_point P lo) hok h01
        set hN : ℕ := (hi - lo).toNat with hhN
        have hhn : ((hN : ℕ) : ℤ) = hi - lo := Int.toNat_of_nonneg (sub_nonneg.mpr hlohi')
        have hhr : ((hN : ℕ) : ℝ) = (hi : ℝ) - lo := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hhn
          push_cast at this ⊢; linarith
        set cl : ℝ := (lo : ℝ) / D with hcl
        set el : ℝ := ((hN : ℕ) : ℝ) / D with hel
        have hclel : cl + el = (hi : ℝ) / D := by rw [hcl, hel, hhr, ← add_div]; ring_nf
        have hM' : ∀ x ∈ Set.Icc cl (cl + el), |gsum3 L x| ≤ M := by
          intro x hx
          rw [hclel] at hx
          exact hM x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hyI : y ∈ Set.Icc cl (cl + el) := ⟨hy.1, by rw [hclel]; exact hy.2⟩
        have hT := taylor3_right hf hf1 hf2 hM' y hyI
        set A : ℝ := (G0.m : ℝ) - G0.r with hAdef
        set B : ℝ := (G1.m : ℝ) - G1.r with hBdef
        set C2 : ℝ := (G2.m : ℝ) - G2.r with hC2def
        set K : ℝ := 3 * C2 * D - (G3.absHi : ℝ) * hN with hKdef
        have hv0 : A / D ≤ gsum L cl := by
          unfold mem at hg0
          have := (abs_le.mp hg0).1
          rw [hAdef, sub_div]; linarith
        have hv1 : B / D ≤ gsum1 L cl := by
          unfold mem at hg1
          have := (abs_le.mp hg1).1
          rw [hBdef, sub_div]; linarith
        have hv2 : C2 / D ≤ gsum2 L cl := by
          unfold mem at hg2
          have := (abs_le.mp hg2).1
          rw [hC2def, sub_div]; linarith
        set t := y - cl with ht
        have ht0 : 0 ≤ t := by linarith [hyI.1]
        have htel : t ≤ el := by linarith [hyI.2]
        set κl : ℝ := K / (3 * D ^ 2) with hκl
        have hκ : κl ≤ gsum2 L cl - M * el / 3 := by
          have e1 : κl = C2 / D - M * el / 3 := by
            rw [hκl, hKdef, hMdef, hel]; field_simp <;> ring
          rw [e1]; linarith
        have hAr : 0 < A / D := by
          apply div_pos _ hP
          have : ((0 : ℤ) : ℝ) < ((G0.m - (G0.r : ℤ) : ℤ) : ℝ) := by exact_mod_cast hA0
          push_cast at this; rw [hAdef]; linarith
        have hbr : (0 : ℝ) < 6 * A * D ^ 3 + 6 * B * hN * D ^ 2 + min K 0 * (hN : ℝ) ^ 2 := by
          have : ((0 : ℤ) : ℝ) < ((6 * (G0.m - (G0.r : ℤ)) * ((2 ^ P : ℕ) : ℤ) * ((2 ^ P : ℕ) : ℤ) *
              ((2 ^ P : ℕ) : ℤ) + 6 * (G1.m - (G1.r : ℤ)) * ((hN : ℕ) : ℤ) * ((2 ^ P : ℕ) : ℤ) *
              ((2 ^ P : ℕ) : ℤ) + min (3 * (G2.m - (G2.r : ℤ)) * ((2 ^ P : ℕ) : ℤ) -
              ((G3.absHi : ℕ) : ℤ) * ((hN : ℕ) : ℤ)) 0 * ((hN : ℕ) : ℤ) * ((hN : ℕ) : ℤ) : ℤ) : ℝ) := by
            exact_mod_cast hQ
          push_cast at this
          rw [← hD, ← hAdef, ← hBdef, ← hC2def, ← hKdef] at this
          have e2 : 6 * A * D ^ 3 + 6 * B * hN * D ^ 2 + min K 0 * (hN : ℝ) ^ 2 =
              6 * A * D * D * D + 6 * B * hN * D * D + min K 0 * hN * hN := by ring
          rw [e2]; exact this
        have hmin : 3 * D ^ 2 * min κl 0 = min K 0 := by rw [hκl]; exact min_scale (by positivity)
        have hQr : 0 < A / D + B / D * el - (-min κl 0) * el ^ 2 / 2 := by
          have e1 : A / D + B / D * el - (-min κl 0) * el ^ 2 / 2 =
              (6 * A * D ^ 3 + 6 * B * hN * D ^ 2 + (3 * D ^ 2 * min κl 0) * (hN : ℝ) ^ 2) / (6 * D ^ 4) := by
            rw [hel]; field_simp <;> ring
          rw [e1, hmin]; exact div_pos hbr (by positivity)
        have hpos := concave_pos hAr (by simp [min_le_right] : (0 : ℝ) ≤ -min κl 0) ht0 htel hQr
        have hcub : M * t ^ 3 / 6 ≤ M * el / 3 * t ^ 2 / 2 := by
          have h1 : t ^ 3 ≤ el * t ^ 2 := by
            have : t ^ 3 = t * t ^ 2 := by ring
            rw [this]; exact mul_le_mul_of_nonneg_right htel (sq_nonneg t)
          have h2 := mul_le_mul_of_nonneg_left h1 hM0
          calc M * t ^ 3 / 6 ≤ M * (el * t ^ 2) / 6 := by gcongr
            _ = M * el / 3 * t ^ 2 / 2 := by ring
        have hlin : B / D * t ≤ gsum1 L cl * t := mul_le_mul_of_nonneg_right hv1 ht0
        have hquad : min κl 0 * t ^ 2 / 2 ≤ (gsum2 L cl - M * el / 3) * t ^ 2 / 2 := by
          have h1 : min κl 0 ≤ gsum2 L cl - M * el / 3 := (min_le_left _ _).trans hκ
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (sq_nonneg t)) (by norm_num)
        have hTt : gsum L cl + gsum1 L cl * t + gsum2 L cl * t ^ 2 / 2 - M * t ^ 3 / 6 ≤ gsum L y := hT
        linarith


theorem rangeOKg_sound {n k : ℕ} {gs : List PG} (hok : ∀ G ∈ gs, PGOk P G) :
    ∀ (d : ℕ) (lo hi : ℤ), rangeOKg P n k gs d lo hi = true →
      ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) ((hi : ℝ) / 2 ^ P), 0 < gsum (gsTriples gs) y := by
  intro d
  induction d with
  | zero => intro lo hi h; exact ivOKg_sound hok h
  | succ d ih =>
    intro lo hi h y hy
    simp only [rangeOKg, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ivOKg_sound hok h y hy
    · rcases le_total y ((((lo + hi) / 2 : ℤ) : ℝ) / 2 ^ P) with hle | hle
      · exact ih lo _ h1 y ⟨hy.1, hle⟩
      · exact ih _ hi h2 y ⟨hle, hy.2⟩

theorem piecesOKg_sound {n k : ℕ} {gs : List PG} (hok : ∀ G ∈ gs, PGOk P G) (d : ℕ) {w : ℤ} (hw : 0 ≤ w) :
    ∀ (c : ℕ) (lo : ℤ), piecesOKg P n k gs d w c lo = true → 0 < c →
      ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) (((lo + c * w : ℤ) : ℝ) / 2 ^ P), 0 < gsum (gsTriples gs) y := by
  intro c
  induction c with
  | zero => intro lo _ hc; exact absurd hc (lt_irrefl 0)
  | succ c ih =>
    intro lo h _ y hy
    simp only [piecesOKg, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hP := two_pow_pos' P
    rcases le_or_gt y (((lo + w : ℤ) : ℝ) / 2 ^ P) with hle | hgt
    · exact rangeOKg_sound hok d lo (lo + w) h1 y ⟨hy.1, hle⟩
    · have hc : 0 < c := by
        rcases Nat.eq_zero_or_pos c with hc0 | hc0
        · exfalso
          subst hc0
          have := hy.2
          simp only [Nat.cast_add, Nat.cast_zero, zero_add, Nat.cast_one, one_mul] at this
          linarith
        · exact hc0
      have e : (((lo + w) + c * w : ℤ) : ℝ) = ((lo + ((c + 1 : ℕ) : ℤ) * w : ℤ) : ℝ) := by push_cast; ring
      exact ih (lo + w) h2 hc y ⟨hgt.le, by rw [e]; exact hy.2⟩


/-! ## Flat data derived from the groups -/

theorem gts_toReal (g : GGroup) (hs : 0 < g.s0d) (hd : 0 < g.dd) :
    g.gts.map GT.toReal = g.triples := by
  unfold GGroup.gts GGroup.triples GGroup.csR
  rw [List.map_zipWith, List.map_zipWith]
  congr 1
  funext j c
  simp only [GT.toReal, aR, cR]
  rw [sk_eq g hs hd j]

theorem gsum_perm_append (A B : List (ℝ × ℝ × ℝ)) (x : ℝ) : gsum (A ++ B) x = gsum (B ++ A) x := by
  rw [gsum_append, gsum_append, add_comm]

/-- `gsTriples` of prepared groups is the concatenation of the groups' triples. -/
theorem gsTriples_eq {n : ℕ} : ∀ {L : List GGroup} {pgs : List PG}, prepGroups P n L = some pgs →
    gsTriples pgs = L.flatMap GGroup.triples
  | [], pgs, h => by simp [prepGroups] at h; subst h; rfl
  | g :: L, pgs, h => by
    simp only [prepGroups, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨G, hG, Gs, hGs, rfl⟩ := h
    have hg : G.g = g := by
      unfold prepGroup at hG
      split_ifs at hG
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hG
      obtain ⟨_, _, _, _, rfl⟩ := hG
      rfl
    simp only [gsTriples, List.flatMap_cons, hg, gsTriples_eq hGs]

theorem prepGroups_pos {n : ℕ} : ∀ {L : List GGroup} {pgs : List PG}, prepGroups P n L = some pgs →
    ∀ g ∈ L, 0 < g.s0d ∧ 0 < g.dd
  | [], _, _ => by simp
  | g :: L, pgs, h => by
    simp only [prepGroups, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨G, hG, Gs, hGs, rfl⟩ := h
    intro g' hg'
    simp only [List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · unfold prepGroup at hG
      split_ifs at hG with hc
      exact ⟨hc.2.2.1, hc.2.2.2.2.1⟩
    · exact prepGroups_pos hGs g' hg'

theorem flatOfGroups_toReal (L : List GGroup) (hpos : ∀ g ∈ L, 0 < g.s0d ∧ 0 < g.dd) (x : ℝ) :
    gsum ((flatOfGroups L).map GT.toReal) x = gsum (L.flatMap GGroup.triples) x := by
  -- flatOfGroups L = last ++ init; L = init ++ [last]
  rcases List.eq_nil_or_concat L with hL | ⟨init, last, hL⟩
  · subst hL; simp [flatOfGroups, gsum]
  · rw [List.concat_eq_append] at hL
    subst hL
    have hpos' : ∀ g ∈ init, 0 < g.s0d ∧ 0 < g.dd := fun g hg => hpos g (by simp [hg])
    have hlast := hpos last (by simp)
    have hinit : (init.flatMap GGroup.gts).map GT.toReal = init.flatMap GGroup.triples := by
      clear hpos
      induction init with
      | nil => rfl
      | cons g L ih =>
        simp only [List.flatMap_cons, List.map_append]
        rw [gts_toReal g (hpos' g (by simp)).1 (hpos' g (by simp)).2,
          ih (fun g' hg' => hpos' g' (by simp [hg']))]
    simp only [flatOfGroups, List.getLast?_append, List.getLast?_singleton, Option.map_some, Option.getD_some,
      List.dropLast_concat, List.map_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Option.some_or]
    rw [gts_toReal last hlast.1 hlast.2, hinit, gsum_perm_append]

theorem contig_sound_g {n k : ℕ} {pgs : List PG} (hok : ∀ G ∈ pgs, PGOk P G) (d : ℕ) :
    ∀ (segs : List Seg) (lo e : ℤ), contigEnd lo segs = some e →
      (∀ s ∈ segs, piecesOKg P n k pgs d s.w s.m s.lo = true) → segs ≠ [] →
      ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) ((e : ℝ) / 2 ^ P), 0 < gsum (gsTriples pgs) y := by
  intro segs
  induction segs with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons s ss ih =>
    intro lo e hc hall _ y hy
    simp only [contigEnd] at hc
    split_ifs at hc with hcond
    obtain ⟨hlo, hm, hw⟩ := hcond
    have hs := hall s (by simp)
    have hpc := piecesOKg_sound hok d (w := (s.w : ℤ)) (by positivity) s.m s.lo hs hm
    rcases le_or_gt y (((s.lo + (s.m : ℤ) * (s.w : ℤ)) : ℤ) / 2 ^ P) with hle | hgt
    · apply hpc
      refine ⟨?_, by exact_mod_cast hle⟩
      rw [hlo]; exact hy.1
    · cases ss with
      | nil =>
        simp only [contigEnd, Option.some.injEq] at hc
        subst hc
        exact absurd hy.2 (not_le.mpr hgt)
      | cons s' ss' =>
        exact ih _ e hc (fun t ht => hall t (by simp [ht])) (by simp) y ⟨hgt.le, hy.2⟩

/-- The sharded upper-bound check with the grid evaluation: the base check on the flat data derived from the
groups (`g(0) < 0`, contiguity and coverage of the segments, the tail), and `segOKg` on every segment. -/
theorem upper_grid_sound (c : Cfg) (L : List GGroup) (segs : List Seg)
    (hb : baseOK c (flatOfGroups L) segs = true) (hs : List.Forall (fun s => segOKg c L s = true) segs) :
    (∀ q ∈ (flatOfGroups L).map GT.toReal, 0 < q.1) ∧ gsum ((flatOfGroups L).map GT.toReal) 0 < 0 ∧
      ∀ y, (c.rn : ℝ) / c.rd ≤ y → 0 < gsum ((flatOfGroups L).map GT.toReal) y := by
  have hne : segs ≠ [] := by
    unfold baseOK at hb
    split at hb
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hb.1.1.1.2.2.2
    · exact absurd hb (by simp)
  obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil segs hne
  have hseg0 := List.forall_iff_forall_mem.mp hs s0 hs0
  unfold segOKg at hseg0
  split at hseg0
  · rename_i pgs hpgs
    have hok := prepGroups_ok hpgs
    have hall : ∀ s ∈ segs, piecesOKg c.P c.n c.k pgs c.depth s.w s.m s.lo = true := by
      intro s hsm
      have := List.forall_iff_forall_mem.mp hs s hsm
      simpa [segOKg, hpgs] using this
    have heq : ∀ x, gsum ((flatOfGroups L).map GT.toReal) x = gsum (gsTriples pgs) x := by
      intro x
      rw [flatOfGroups_toReal L (prepGroups_pos hpgs) x, gsTriples_eq hpgs]
    -- base part: as in upper_sharded_sound
    generalize hfd : flatOfGroups L = fd at heq hb ⊢
    unfold baseOK at hb
    cases hp : prepAll c.P fd with
    | none => simp [hp] at hb
    | some pts =>
      cases pts with
      | nil => simp [hp] at hb
      | cons T R =>
        simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨⟨⟨hpos, hcov⟩, hg0⟩, htail⟩ := hb
        obtain ⟨hrn, hrd, hYd, _⟩ := hpos
        have hF := prepAll_ok hp
        have hL := forall₂_pos hF
        have hP := two_pow_pos' c.P
        refine ⟨hL, ?_, ?_⟩
        · split at hg0
          · rename_i G0 G1 h01
            have := (mem_sum01 (mem_point c.P 0) hF h01).1
            simp only [Int.cast_zero, zero_div] at this
            exact isNeg_sound this hg0
          · exact absurd hg0 (by simp)
        · split at hcov
          · rename_i e he
            simp only [decide_eq_true_eq] at hcov
            have hrange := contig_sound_g hok c.depth segs _ e he hall hne
            cases hF with
            | cons hT hR =>
              rename_i tT ts
              have hYB := mem_ofRat c.P (c.Yn : ℤ) c.Yd hYd
              simp only [Int.cast_natCast] at hYB
              obtain ⟨tc1, tc2, tc3, tc4, tc5⟩ := tailOK_sound hT hR hYB htail
              have htailpos := tail_pos (R := ts.map GT.toReal) (Y := (c.Yn : ℝ) / c.Yd)
                (by have := hT.ha; simpa [GT.toReal] using this) tc1 tc2 tc3 tc4 tc5
              intro y hy
              have hrdr : (0 : ℝ) < c.rd := by exact_mod_cast hrd
              have hYdr : (0 : ℝ) < c.Yd := by exact_mod_cast hYd
              rcases le_or_gt y ((c.Yn : ℝ) / c.Yd) with hyY | hyY
              · rw [heq]
                apply hrange
                constructor
                · have h1 : ((c.rn * 2 ^ c.P / c.rd : ℕ) : ℝ) * c.rd ≤ c.rn * 2 ^ c.P := by
                    exact_mod_cast Nat.div_mul_le_self (c.rn * 2 ^ c.P) c.rd
                  have h2 : ((c.rn * 2 ^ c.P / c.rd : ℕ) : ℝ) / 2 ^ c.P ≤ (c.rn : ℝ) / c.rd := by
                    rw [div_le_div_iff₀ hP hrdr]; linarith
                  simp only [Int.cast_natCast]
                  linarith
                · have h3 : (((c.Yn * 2 ^ c.P : ℕ) : ℤ) : ℝ) ≤ ((e * (c.Yd : ℤ) : ℤ) : ℝ) := by
                    exact_mod_cast hcov
                  push_cast at h3
                  have h4 : (c.Yn : ℝ) / c.Yd ≤ (e : ℝ) / 2 ^ c.P := by
                    rw [div_le_div_iff₀ hYdr hP]; linarith
                  linarith
              · have := htailpos y hyY.le
                simpa [GT.toReal] using this
          · exact absurd hcov (by simp)
  · exact absurd hseg0 (by simp)

end SignUnc.Chk
