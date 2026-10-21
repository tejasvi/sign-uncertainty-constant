import SignUnc.GridSound
import SignUnc.Jets
import SUCert.Jet

/-!
# Soundness of checker v4 (`SUCert.Jet`), part 1: series, moments, products
-/

namespace SignUnc.Chk

open Ival Ival.Ball Ival.CDisc Real Complex Finset

variable {P : ℕ}

/-- The balls `bs` contain the reals `xs` (entrywise, same length). -/
abbrev MemL (P : ℕ) (xs : List ℝ) (bs : List Ball) : Prop := List.Forall₂ (fun x b => mem P x b) xs bs

theorem listSum_range (f : ℕ → ℝ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem memL_zeroL (n : ℕ) : MemL P ((List.range n).map fun _ => (0 : ℝ)) (zeroL n) := by
  unfold zeroL
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.replicate_succ]
    exact List.Forall₂.cons mem_zero_ball (by simpa [Function.comp_def] using ih)

theorem memL_addL {xs ys : List ℝ} {as bs : List Ball} (h1 : MemL P xs as) (h2 : MemL P ys bs) :
    MemL P (List.zipWith (· + ·) xs ys) (addL as bs) := by
  unfold addL
  induction h1 generalizing ys bs with
  | nil => simp
  | cons hx _ ih =>
    cases h2 with
    | nil => simp
    | cons hy h2' => exact List.Forall₂.cons (mem_add hx hy) (ih h2')

theorem zipWith_add_range (f g : ℕ → ℝ) (n : ℕ) :
    List.zipWith (· + ·) ((List.range n).map f) ((List.range n).map g) = (List.range n).map fun i => f i + g i := by
  rw [List.zipWith_map]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.zipWith_append (by simp), ih]
    simp

theorem memL_powsW {a : ℝ} {A : Ball} (hA : mem P a A) :
    ∀ (n : ℕ) {w : ℝ} {W : Ball}, mem P w W → MemL P ((List.range n).map fun p => w * a ^ p) (powsW P A n W) := by
  intro n
  induction n with
  | zero => intro w W _; simp [powsW]
  | succ n ih =>
    intro w W hw
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.Forall₂.cons (by simpa using hw) ?_
    have := ih (mem_mul hw hA)
    convert this using 2
    funext p; simp [pow_succ]; ring

/-- Entry `p` of the interleaved powers: `x b^(p/2)` (even `p`), `y b^(p/2)` (odd `p`). -/
noncomputable def pw2R (x y b : ℝ) (p : ℕ) : ℝ := if p % 2 = 0 then x * b ^ (p / 2) else y * b ^ (p / 2)

theorem pw2R_succ (x y b : ℝ) (p : ℕ) : pw2R x y b (p + 1) = pw2R y (x * b) b p := by
  unfold pw2R
  rcases Nat.even_or_odd p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have h1 : (q + q + 1) % 2 = 1 := by omega
    have h2 : (q + q) % 2 = 0 := by omega
    have h3 : (q + q + 1) / 2 = q := by omega
    have h4 : (q + q) / 2 = q := by omega
    simp [h1, h2, h3, h4]
  · have h1 : (2 * q + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * q + 1) % 2 = 1 := by omega
    have h3 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    have h4 : (2 * q + 1) / 2 = q := by omega
    simp [h1, h2, h3, h4, pow_succ]; ring

theorem memL_pows2 {b : ℝ} {B : Ball} (hB : mem P b B) :
    ∀ (n : ℕ) {x y : ℝ} {X Y : Ball}, mem P x X → mem P y Y →
      MemL P ((List.range n).map (pw2R x y b)) (pows2 P B n X Y) := by
  intro n
  induction n with
  | zero => intro x y X Y _ _; simp [pows2]
  | succ n ih =>
    intro x y X Y hx hy
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.Forall₂.cons (by simpa [pw2R] using hx) ?_
    have := ih hy (mem_mul hx hB)
    convert this using 2
    funext p; simp [pw2R_succ]

theorem memL_eserAux {α β : ℝ} {al be2 : Ball} (hα : mem P α al) (hβ : mem P (2 * β) be2) :
    ∀ (fuel j : ℕ) {e0 e1 : Ball}, mem P (ecoef α β j) e0 → mem P (ecoef α β (j + 1)) e1 →
      MemL P ((List.range fuel).map fun i => ecoef α β (j + i)) (eserAux P al be2 fuel j e0 e1) := by
  intro fuel
  induction fuel with
  | zero => intro j e0 e1 _ _; simp [eserAux]
  | succ fuel ih =>
    intro j e0 e1 h0 h1
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.Forall₂.cons (by simpa using h0) ?_
    have h2 : mem P (ecoef α β (j + 2)) (divNat (j + 2) (add (mul P al e1) (mul P be2 e0))) := by
      have := mem_divNat (by omega : 0 < j + 2) (mem_add (mem_mul hα h1) (mem_mul hβ h0))
      rw [ecoef_succ_succ]
      convert this using 1
      push_cast; ring
    have := ih (j + 1) h1 h2
    convert this using 2
    funext i; simp only [Function.comp_apply]; congr 1; omega

theorem memL_eser {α β : ℝ} {al be : Ball} (hα : mem P α al) (hβ : mem P β be) (n : ℕ) :
    MemL P ((List.range (n + 1)).map (ecoef α β)) (eser P n al be) := by
  have h2 : mem P (2 * β) (mulInt 2 be) := by simpa using mem_mulInt 2 hβ
  have := memL_eserAux hα h2 (n + 1) 0 (by simpa using mem_ofInt P 1) (by simpa using hα)
  unfold eser
  simpa using this

/-- Real moments `Σ_k w_k a_k^p`. -/
noncomputable def momR (L : List (ℝ × ℝ)) (p : ℕ) : ℝ := (L.map fun r => r.1 * r.2 ^ p).sum

theorem memL_momW (n : ℕ) {L : List (ℝ × ℝ)} {LB : List (Ball × Ball)}
    (h : List.Forall₂ (fun (r : ℝ × ℝ) (b : Ball × Ball) => mem P r.1 b.1 ∧ mem P r.2 b.2) L LB) :
    MemL P ((List.range (n + 1)).map (momR L)) (momW P n LB) := by
  induction h with
  | nil =>
    have e : momR [] = fun _ => 0 := by funext p; simp [momR]
    rw [e]; exact memL_zeroL (n + 1)
  | cons hr _ ih =>
    rename_i r b L' LB' _
    obtain ⟨w, a⟩ := b
    simp only [momW]
    have := memL_addL (memL_powsW hr.2 (n + 1) hr.1) ih
    rw [zipWith_add_range] at this
    convert this using 2
    funext p; simp [momR]

/-- Real moments `Σ_k pw2R x_k y_k b_k p`. -/
noncomputable def momR2 (L : List (ℝ × ℝ × ℝ)) (p : ℕ) : ℝ := (L.map fun r => pw2R r.1 r.2.1 r.2.2 p).sum

theorem memL_momW2 (n : ℕ) {L : List (ℝ × ℝ × ℝ)} {LB : List (Ball × Ball × Ball)}
    (h : List.Forall₂ (fun (r : ℝ × ℝ × ℝ) (b : Ball × Ball × Ball) =>
      mem P r.1 b.1 ∧ mem P r.2.1 b.2.1 ∧ mem P r.2.2 b.2.2) L LB) :
    MemL P ((List.range (n + 1)).map (momR2 L)) (momW2 P n LB) := by
  induction h with
  | nil =>
    have e : momR2 [] = fun _ => 0 := by funext p; simp [momR2]
    rw [e]; exact memL_zeroL (n + 1)
  | cons hr _ ih =>
    rename_i r b L' LB' _
    obtain ⟨x, y, bb⟩ := b
    simp only [momW2]
    have := memL_addL (memL_pows2 hr.2.2 (n + 1) hr.1 hr.2.1) ih
    rw [zipWith_add_range] at this
    convert this using 2
    funext p; simp [momR2]

theorem memL_divFactAux {f : ℕ → ℝ} :
    ∀ (N p : ℕ) {L : List Ball}, MemL P ((List.range' p N).map f) L →
      MemL P ((List.range' p N).map fun i => f i / (i.factorial : ℝ)) (divFactAux p p.factorial L) := by
  intro N
  induction N with
  | zero => intro p L h; cases h; simp [divFactAux]
  | succ N ih =>
    intro p L h
    rw [List.range'_succ, List.map_cons] at h
    cases h with
    | cons hx h' =>
      rename_i b L'
      rw [List.range'_succ, List.map_cons]
      simp only [divFactAux]
      refine List.Forall₂.cons (mem_divNat (Nat.factorial_pos p) hx) ?_
      have := ih (p + 1) h'
      rwa [Nat.factorial_succ, mul_comm] at this

theorem memL_divFact {f : ℕ → ℝ} {N : ℕ} {L : List Ball} (h : MemL P ((List.range N).map f) L) :
    MemL P ((List.range N).map fun i => f i / (i.factorial : ℝ)) (divFact L) := by
  rw [List.range_eq_range'] at h ⊢
  exact memL_divFactAux N 0 h

theorem mem_dot {xs ys : List ℝ} {as bs : List Ball} (h1 : MemL P xs as) (h2 : MemL P ys bs) :
    mem P (List.zipWith (· * ·) xs ys).sum (dot P as bs) := by
  induction h1 generalizing ys bs with
  | nil => cases h2 <;> simp [dot, mem_zero_ball]
  | cons hx _ ih =>
    cases h2 with
    | nil => simp [dot, mem_zero_ball]
    | cons hy h2' => simpa [dot] using mem_add (mem_mul hx hy) (ih h2')

theorem rev_range_succ (g : ℕ → ℝ) (j : ℕ) :
    ((List.range (j + 1)).map g).reverse = g j :: ((List.range j).map g).reverse := by
  rw [List.range_succ, List.map_append, List.reverse_append]; simp

theorem zipRevSum (μR gR : ℕ → ℝ) : ∀ (j N : ℕ), j < N →
    (List.zipWith (· * ·) ((List.range N).map μR) ((List.range (j + 1)).map gR).reverse).sum =
      ∑ p ∈ range (j + 1), μR p * gR (j - p) := by
  intro j
  induction j generalizing μR with
  | zero =>
    intro N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [List.range_succ_eq_map]; simp
  | succ j ih =>
    intro N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [rev_range_succ, List.range_succ_eq_map, List.map_cons, List.map_map, List.zipWith_cons_cons, List.sum_cons,
      ih (μR ∘ Nat.succ) N' (by omega), sum_range_succ' (fun p => μR p * gR (j + 1 - p))]
    simp only [Function.comp_apply, Nat.succ_eq_add_one, Nat.sub_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl (fun p hp => ?_)
    congr 2; omega

theorem memL_convAux {N : ℕ} {μR gR : ℕ → ℝ} {μ : List Ball} (hμ : MemL P ((List.range N).map μR) μ) :
    ∀ (M k : ℕ) {gs rg : List Ball}, MemL P ((List.range' k M).map gR) gs → MemL P ((List.range k).map gR).reverse rg →
      MemL P ((List.range' k M).map fun j =>
        (List.zipWith (· * ·) ((List.range N).map μR) ((List.range (j + 1)).map gR).reverse).sum)
        (convAux P μ gs rg) := by
  intro M
  induction M with
  | zero => intro k gs rg hg _; cases hg; simp [convAux]
  | succ M ih =>
    intro k gs rg hg hr
    rw [List.range'_succ, List.map_cons] at hg
    cases hg with
    | cons hgk hg' =>
      rename_i g gs'
      have hr' : MemL P ((List.range (k + 1)).map gR).reverse (g :: rg) := by
        rw [rev_range_succ]; exact List.Forall₂.cons hgk hr
      rw [List.range'_succ, List.map_cons]
      simp only [convAux]
      exact List.Forall₂.cons (mem_dot hμ hr') (ih (k + 1) hg' hr')

/-- Entry `j` of `conv g μ` contains `Σ_{p ≤ j} μ_p g_{j-p}`. -/
theorem memL_conv {n : ℕ} {μR gR : ℕ → ℝ} {μ g : List Ball} (hμ : MemL P ((List.range (n + 1)).map μR) μ)
    (hg : MemL P ((List.range (n + 1)).map gR) g) :
    MemL P ((List.range (n + 1)).map fun j => ∑ p ∈ range (j + 1), μR p * gR (j - p)) (conv P g μ) := by
  have := memL_convAux hμ (n + 1) 0 (rg := []) (by rw [← List.range_eq_range']; exact hg) (by simp)
  rw [← List.range_eq_range'] at this
  unfold conv
  convert this using 1
  refine List.map_congr_left (fun j hj => ?_)
  rw [zipRevSum μR gR j (n + 1) (by simpa using hj)]

end SignUnc.Chk
