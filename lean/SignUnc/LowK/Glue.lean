import SignUnc.LowK.Defs

/-!
# Kernel shards of the lower check: glue lemmas (core Lean only)
-/

namespace SignUnc.Chk

open Ival

theorem lsegOK_of_lsegM {c : LCfg} {gs : List GGroup} {cos : List (Nat × Nat × Int × Nat)} {ps : List PPiece}
    {s : LSeg} {moms : List (List (List Ball))} (hm : ps.map (pieceMoms c.P s.M s.N) = moms)
    (h : lsegM c gs cos ps s moms = true) : lsegOK c gs cos ps s = true := by
  unfold lsegOK
  unfold lsegM at h
  rw [hm]
  exact h

theorem pieceMomsAux_take (P : Nat) (c e : Ball) :
    ∀ (K : Nat) (q : List Ball) {N N' : Nat}, N ≤ N' →
      pieceMomsAux P N c e K q = (pieceMomsAux P N' c e K q).map (·.take N)
  | 0, _, _, _, _ => rfl
  | K + 1, q, N, N', h => by
    simp only [pieceMomsAux, List.map_cons]
    rw [← pieceMomsAux_take P c e K (mulLin P c e q) h, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem pieceMoms_take {P M N N' : Nat} (h : N ≤ N') (pc : PPiece) :
    pieceMoms P M N pc = (pieceMoms P M N' pc).map (·.take N) :=
  pieceMomsAux_take P _ _ (M + 1) _ h

theorem pOK_of {P n k D L : Nat} {gs : List GGroup} {cos : List (Nat × Nat × Int × Nat)}
    {psi : List (Int × Nat)} {eps : Nat} {ps : List PPiece} {sps : List (List GSpec)}
    (hc : chainOK 0 ps = true) (hl : ps.length = sps.length) (hne : ps.zip sps ≠ [])
    (h : ∀ x ∈ ps.zip sps, ppOK P n k D L gs cos psi eps x = true) :
    pOK P n k D L gs cos psi eps ps sps = true := by
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
  have h0 := h x0 hx0
  unfold pOK
  unfold ppOK at h h0
  cases hp : prepGroupsV P n gs with
  | none => rw [hp] at h0; exact absurd h0 (by simp)
  | some pgs =>
    simp only [hp] at h
    simp only [hc, hl, decide_true, Bool.true_and, List.all_eq_true]
    exact h

theorem zip_map_fst_snd {α β : Type} : ∀ l : List (α × β), (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | x :: l => by simp [zip_map_fst_snd l]

theorem all_of_getD {α : Type} (l : List α) (d : α) (p : α → Bool)
    (h : ∀ i < l.length, p (l.getD i d) = true) : ∀ x ∈ l, p x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i hi
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

end SignUnc.Chk

namespace SignUnc.LowData

open SignUnc.Chk Ival

theorem momsFor20 (km20 : lowP.map (pieceMoms 128 20 25) = MomsLit20) :
    lowP.map (pieceMoms 128 20 25) = momsFor 20 25 := by
  rw [momsFor, ite_eq_left rfl, km20]

theorem momsFor16 {N : Nat} (hN : N ≤ 135) (km16 : lowP.map (pieceMoms 128 16 135) = MomsLit16) :
    lowP.map (pieceMoms 128 16 N) = momsFor 16 N := by
  rw [momsFor, ite_eq_right (by decide), ← km16, List.map_map]
  apply List.map_congr_left
  intro pc _
  exact pieceMoms_take hN pc

end SignUnc.LowData
