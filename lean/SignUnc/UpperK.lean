import SignUnc.PieceSound
import SUCert.JetK

/-!
# Soundness of checker v4 for the whole range: `upper_v4_sound`

`baseOK4` (contiguous segments from `⌊r 2^P⌋` up to `Y`, `g(0) < 0`, tail at `Y`) and `segOK4` for every segment
give positivity of `g` on `[r, ∞)` and `g(0) < 0`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real Finset

variable {P : ℕ}

theorem forall₂_pos4 : ∀ {L : List GGroup} {pgs : List PG4},
    List.Forall₂ (fun (g : GGroup) (G : PG4) => PG4Ok P G ∧ G.G.g = g) L pgs → ∀ g ∈ L, 0 < g.s0d ∧ 0 < g.dd
  | [], [], _ => by simp
  | g :: L, G :: pgs, List.Forall₂.cons hG h => by
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg''
    · rw [← hG.2]; exact ⟨hG.1.hG.hs0d, hG.1.hG.hdd⟩
    · exact forall₂_pos4 h g' hg''

theorem prepGroups4_pos {n : ℕ} {L : List GGroup} {pgs : List PG4} (h : prepGroups4 P n L = some pgs) :
    ∀ g ∈ L, 0 < g.s0d ∧ 0 < g.dd := forall₂_pos4 (prepGroups4_ok h)

theorem contig_sound4 (c : Cfg) (L : List GGroup) :
    ∀ (segs : List Seg4) (lo e : ℤ), contigEnd4 lo segs = some e →
      (∀ s ∈ segs, segOK4 c L s = true) → segs ≠ [] →
      ∀ y, (lo : ℝ) / 2 ^ c.P ≤ y → y ≤ (e : ℝ) / 2 ^ c.P → 0 < gsum (L.flatMap GGroup.triples) y := by
  intro segs
  induction segs with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons s ss ih =>
    intro lo e hc hall _ y hy1 hy2
    simp only [contigEnd4] at hc
    split_ifs at hc with hcond
    obtain ⟨hlo, hne, hws⟩ := hcond
    have hpos : ∀ r ∈ s.ws, 0 < r.2 := by
      intro r hr
      have := List.all_eq_true.mp hws r hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    have hs := hall s (by simp)
    rcases le_or_gt y ((runsEnd s.lo s.ws : ℝ) / 2 ^ c.P) with hle | hgt
    · exact segOK4_sound c L s hs hne hpos y (by rw [hlo]; exact hy1) hle
    · cases ss with
      | nil =>
        simp only [contigEnd4, Option.some.injEq] at hc
        subst hc
        exact absurd hy2 (not_le.mpr hgt)
      | cons s' ss' =>
        exact ih _ e hc (fun t ht => hall t (by simp [ht])) (by simp) y hgt.le hy2

theorem upper_v4_sound (c : Cfg) (L : List GGroup) (segs : List Seg4)
    (hb : baseOK4 c (flatOfGroups L) segs = true) (hs : List.Forall (fun s => segOK4 c L s = true) segs) :
    (∀ q ∈ (flatOfGroups L).map GT.toReal, 0 < q.1) ∧ gsum ((flatOfGroups L).map GT.toReal) 0 < 0 ∧
      ∀ y, (c.rn : ℝ) / c.rd ≤ y → 0 < gsum ((flatOfGroups L).map GT.toReal) y := by
  have hne : segs ≠ [] := by
    unfold baseOK4 at hb
    split at hb
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hb.1.1.1.2.2.2
    · exact absurd hb (by simp)
  obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil segs hne
  have hseg0 := List.forall_iff_forall_mem.mp hs s0 hs0
  unfold segOK4 at hseg0
  split at hseg0
  · rename_i pgs hpgs
    have hall : ∀ s ∈ segs, segOK4 c L s = true := fun s hsm => List.forall_iff_forall_mem.mp hs s hsm
    have heq : ∀ x, gsum ((flatOfGroups L).map GT.toReal) x = gsum (L.flatMap GGroup.triples) x :=
      fun x => flatOfGroups_toReal L (prepGroups4_pos hpgs) x
    generalize hfd : flatOfGroups L = fd at heq hb ⊢
    unfold baseOK4 at hb
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
            have hrange := contig_sound4 c L segs _ e he hall hne
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
