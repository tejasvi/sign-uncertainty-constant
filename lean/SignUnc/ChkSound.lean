import SignUnc.Tail
import SUCert.Chk
import SignUnc.Ival.SoundTrig

/-!
# Soundness of the upper-bound checker

`checkUpper_sound`: if `checkUpper c data = true`, then for the real pairs `L = data.map GT.toReal`,
`gsum L 0 < 0` and `gsum L > 0` on `[rn/rd, ∞)`.
-/

namespace SignUnc.Chk

open Ival Ival.Ball Real SignUnc

/-- The real pair `(a, s, c)` of a data entry. -/
noncomputable def GT.toReal (t : GT) : ℝ × ℝ × ℝ :=
  ((t.an : ℝ) / t.ad, (t.sn : ℝ) / t.sd, (t.cn : ℝ) / t.cd)

/-- `p` holds balls for the real data of `t`. -/
structure PTOk (P : ℕ) (t : GT) (p : PT) : Prop where
  ha : 0 < (t.an : ℝ) / t.ad
  hA : mem P ((t.an : ℝ) / t.ad) p.A
  hS : mem P ((t.sn : ℝ) / t.sd) p.S
  hC : mem P ((t.cn : ℝ) / t.cd) p.C
  hAi : mem P (1 / ((t.an : ℝ) / t.ad)) p.Ai
  hQ : mem P (2 / Real.sqrt ((t.an : ℝ) / t.ad)) p.Q

theorem mem_twoOverSqrt {P an ad : ℕ} {Q : Ball} (had : 0 < ad) (h : twoOverSqrt P an ad = some Q) :
    mem P (2 / Real.sqrt ((an : ℝ) / ad)) Q := by
  simp only [twoOverSqrt] at h
  split_ifs at h with hc
  obtain ⟨han, h1, h2⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  set N := 4 * ad * 2 ^ (2 * P) / an with hNdef
  set m := isqrt N
  have hP := two_pow_pos' P
  have hanr : (0 : ℝ) < an := by exact_mod_cast han
  have hadr : (0 : ℝ) < ad := by exact_mod_cast had
  have hq : 0 < (an : ℝ) / ad := div_pos hanr hadr
  set v := 2 / Real.sqrt ((an : ℝ) / ad) with hv
  have hv0 : 0 ≤ v := by positivity
  have hvsq : (v * 2 ^ P) ^ 2 = 4 * ad * 2 ^ (2 * P) / an := by
    rw [hv, mul_pow, div_pow, Real.sq_sqrt hq.le, ← pow_mul, mul_comm P 2]
    field_simp
    norm_num
  have hN1 : (N : ℝ) ≤ 4 * ad * 2 ^ (2 * P) / an := by
    rw [le_div_iff₀ hanr]
    have := Nat.div_mul_le_self (4 * ad * 2 ^ (2 * P)) an
    exact_mod_cast this
  have hN2 : 4 * ad * 2 ^ (2 * P) / (an : ℝ) < N + 1 := by
    rw [div_lt_iff₀ hanr]
    have := Nat.lt_div_mul_add (a := 4 * ad * 2 ^ (2 * P)) han
    have h3 : (4 * ad * 2 ^ (2 * P) : ℕ) < (N + 1) * an := by rw [add_mul, one_mul]; exact this
    exact_mod_cast h3
  have hm1 : ((m : ℝ)) ^ 2 ≤ (v * 2 ^ P) ^ 2 := by
    rw [hvsq]
    have : ((m * m : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    push_cast at this
    nlinarith
  have hm2 : (v * 2 ^ P) ^ 2 < ((m : ℝ) + 1) ^ 2 := by
    rw [hvsq]
    have h2' : N + 1 ≤ (m + 1) * (m + 1) := h2
    have : ((N + 1 : ℕ) : ℝ) ≤ (((m + 1) * (m + 1) : ℕ) : ℝ) := by exact_mod_cast h2'
    push_cast at this
    nlinarith
  have hvP : 0 ≤ v * 2 ^ P := by positivity
  have hle : (m : ℝ) ≤ v * 2 ^ P := (pow_le_pow_iff_left₀ (by positivity) hvP two_ne_zero).mp hm1
  have hlt : v * 2 ^ P < (m : ℝ) + 1 := (pow_lt_pow_iff_left₀ hvP (by positivity) two_ne_zero).mp hm2
  have e1 : (m : ℝ) / 2 ^ P ≤ v := by rw [div_le_iff₀ hP]; linarith
  have e2 : v ≤ ((m : ℝ) + 1) / 2 ^ P := by rw [le_div_iff₀ hP]; linarith
  have e3 : ((m : ℝ) + 1) / 2 ^ P = (m : ℝ) / 2 ^ P + 1 / 2 ^ P := add_div _ _ _
  have e4 : (0 : ℝ) ≤ 1 / 2 ^ P := by positivity
  unfold mem
  simp only [Int.cast_natCast, Nat.cast_one]
  rw [abs_le]
  constructor <;> linarith

theorem prep_ok {P : ℕ} {t : GT} {p : PT} (h : prep P t = some p) : PTOk P t p := by
  unfold prep at h
  split_ifs at h with hc
  obtain ⟨han, had, hsd, hcd⟩ := hc
  cases hq : twoOverSqrt P t.an t.ad with
  | none => simp [hq] at h
  | some Q =>
    simp only [hq, Option.some.injEq] at h
    subst h
    have hanr : (0 : ℝ) < t.an := by exact_mod_cast han
    have hadr : (0 : ℝ) < t.ad := by exact_mod_cast had
    refine ⟨div_pos hanr hadr, ?_, mem_ofRat P t.sn t.sd hsd, mem_ofRat P t.cn t.cd hcd, ?_,
      mem_twoOverSqrt had hq⟩
    · have := mem_ofRat P (t.an : ℤ) t.ad had
      simpa using this
    · have := mem_ofRat P (t.ad : ℤ) t.an han
      rw [one_div_div]
      simpa using this

theorem prepAll_ok {P : ℕ} : ∀ {data : List GT} {pts : List PT}, prepAll P data = some pts →
    List.Forall₂ (PTOk P) data pts
  | [], pts, h => by simp [prepAll] at h; subst h; exact List.Forall₂.nil
  | t :: L, pts, h => by
    unfold prepAll at h
    cases hp : prep P t with
    | none => simp [hp] at h
    | some p =>
      cases hL : prepAll P L with
      | none => simp [hp, hL] at h
      | some ps =>
        simp only [hp, hL, Option.some.injEq] at h
        subst h
        exact List.Forall₂.cons (prep_ok hp) (prepAll_ok hL)

section terms

variable {P n k : ℕ} {t : GT} {p : PT} {y : ℝ} {Y : Ball}

theorem mem_term01 (hp : PTOk P t p) (hY : mem P y Y) {u v : Ball}
    (h : term01 P n k p Y = some (u, v)) :
    mem P (t.toReal.2.2 * (gb t.toReal.1 t.toReal.2.1 y + gbh t.toReal.1 t.toReal.2.1 y)) u ∧
    mem P (t.toReal.2.2 * (gb1 t.toReal.1 t.toReal.2.1 y + gbh1 t.toReal.1 t.toReal.2.1 y)) v := by
  simp only [term01, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨E1, hE1, E2, hE2, H, hH, ⟨Cs, Sn⟩, hcs, hu, hv⟩ := h
  subst hu hv
  simp only [GT.toReal]
  set a : ℝ := (t.an : ℝ) / t.ad
  set s : ℝ := (t.sn : ℝ) / t.sd
  set c : ℝ := (t.cn : ℝ) / t.cd
  have hpi := mem_piB P
  have hd1 : mem P (y - s) (sub Y p.S) := mem_sub hY hp.hS
  have hd2 : mem P (y + s) (add Y p.S) := mem_add hY hp.hS
  have hpa : mem P (π * a) (mul P (piB P) p.A) := mem_mul hpi hp.hA
  have hE1' : mem P (Real.exp (-π * a * (y - s) ^ 2)) E1 := by
    have := mem_expB' (mem_neg (mem_mul hpa (mem_mul hd1 hd1))) hE1
    rw [show -π * a * (y - s) ^ 2 = -(π * a * ((y - s) * (y - s))) by ring]; exact this
  have hE2' : mem P (Real.exp (-π * a * (y + s) ^ 2)) E2 := by
    have := mem_expB' (mem_neg (mem_mul hpa (mem_mul hd2 hd2))) hE2
    rw [show -π * a * (y + s) ^ 2 = -(π * a * ((y + s) * (y + s))) by ring]; exact this
  have hH' : mem P (Real.exp (-π * y ^ 2 / a)) H := by
    have := mem_expB' (mem_neg (mem_mul hpi (mem_mul (mem_mul hY hY) hp.hAi))) hH
    rw [show -π * y ^ 2 / a = -(π * (y * y * (1 / a))) by ring]; exact this
  have hcs' := mem_cosSinTurn (mem_mul hp.hS hY) hcs
  rw [show 2 * π * (s * y) = 2 * π * s * y by ring] at hcs'
  obtain ⟨hC', hS'⟩ := hcs'
  have hQH : mem P (2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a)) (mul P p.Q H) := mem_mul hp.hQ hH'
  have hpiy : mem P (π * (y * (1 / a))) (mul P (piB P) (mul P Y p.Ai)) := mem_mul hpi (mem_mul hY hp.hAi)
  have hpis : mem P (π * s) (mul P (piB P) p.S) := mem_mul hpi hp.hS
  constructor
  · have := mem_mul hp.hC (mem_add (mem_add hE1' hE2') (mem_mul hQH hC'))
    have e : c * (gb a s y + gbh a s y) = c * (Real.exp (-π * a * (y - s) ^ 2) +
        Real.exp (-π * a * (y + s) ^ 2) +
        2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * Real.cos (2 * π * s * y)) := by
      unfold gb gbh; ring
    rw [e]; exact this
  · have hgb1 := mem_neg (mem_mul (mem_mulInt 2 hpa) (mem_add (mem_mul hd1 hE1') (mem_mul hd2 hE2')))
    have hgbh1 := mem_mul hQH (mem_sub (mem_neg (mem_mul (mem_mulInt 2 hpiy) hC'))
      (mem_mul (mem_mulInt 2 hpis) hS'))
    have := mem_mul hp.hC (mem_add hgb1 hgbh1)
    have e : c * (gb1 a s y + gbh1 a s y) = c * (-((2 : ℤ) * (π * a) * ((y - s) * Real.exp (-π * a * (y - s) ^ 2) +
        (y + s) * Real.exp (-π * a * (y + s) ^ 2))) +
        2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) * (-((2 : ℤ) * (π * (y * (1 / a))) * Real.cos (2 * π * s * y)) -
          (2 : ℤ) * (π * s) * Real.sin (2 * π * s * y))) := by
      unfold gb1 gbh1; push_cast; ring
    rw [e]; exact this

theorem mem_term2 (hp : PTOk P t p) (hY : mem P y Y) {u : Ball} (h : term2 P n k p Y = some u) :
    mem P (t.toReal.2.2 * (gb2 t.toReal.1 t.toReal.2.1 y + gbh2 t.toReal.1 t.toReal.2.1 y)) u := by
  simp only [term2, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨E1, hE1, E2, hE2, H, hH, ⟨Cs, Sn⟩, hcs, hu⟩ := h
  subst hu
  simp only [GT.toReal]
  set a : ℝ := (t.an : ℝ) / t.ad
  set s : ℝ := (t.sn : ℝ) / t.sd
  set c : ℝ := (t.cn : ℝ) / t.cd
  have hpi := mem_piB P
  have hd1 : mem P (y - s) (sub Y p.S) := mem_sub hY hp.hS
  have hd2 : mem P (y + s) (add Y p.S) := mem_add hY hp.hS
  have hpa : mem P (π * a) (mul P (piB P) p.A) := mem_mul hpi hp.hA
  have hE1' : mem P (Real.exp (-π * a * (y - s) ^ 2)) E1 := by
    have := mem_expH (mem_neg (mem_mul hpa (mem_mul hd1 hd1))) hE1
    rw [show -π * a * (y - s) ^ 2 = -(π * a * ((y - s) * (y - s))) by ring]; exact this
  have hE2' : mem P (Real.exp (-π * a * (y + s) ^ 2)) E2 := by
    have := mem_expH (mem_neg (mem_mul hpa (mem_mul hd2 hd2))) hE2
    rw [show -π * a * (y + s) ^ 2 = -(π * a * ((y + s) * (y + s))) by ring]; exact this
  have hH' : mem P (Real.exp (-π * y ^ 2 / a)) H := by
    have := mem_expH (mem_neg (mem_mul hpi (mem_mul (mem_mul hY hY) hp.hAi))) hH
    rw [show -π * y ^ 2 / a = -(π * (y * y * (1 / a))) by ring]; exact this
  have hcs' := mem_cosSinTurnC (mem_mul hp.hS hY) hcs
  rw [show 2 * π * (s * y) = 2 * π * s * y by ring] at hcs'
  obtain ⟨hC', hS'⟩ := hcs'
  have hQH : mem P (2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a)) (mul P p.Q H) := mem_mul hp.hQ hH'
  have hpiy : mem P (π * (y * (1 / a))) (mul P (piB P) (mul P Y p.Ai)) := mem_mul hpi (mem_mul hY hp.hAi)
  have hpis : mem P (π * s) (mul P (piB P) p.S) := mem_mul hpi hp.hS
  have hpa2 := mem_mul hpa hpa
  have hc1 := mem_sub (mem_mulInt 4 (mem_mul hpa2 (mem_mul hd1 hd1))) (mem_mulInt 2 hpa)
  have hc2 := mem_sub (mem_mulInt 4 (mem_mul hpa2 (mem_mul hd2 hd2))) (mem_mulInt 2 hpa)
  have hgb2 := mem_add (mem_mul hc1 hE1') (mem_mul hc2 hE2')
  have hk1 := mem_sub (mem_sub (mem_mulInt 4 (mem_mul hpiy hpiy)) (mem_mulInt 2 (mem_mul hpi hp.hAi)))
    (mem_mulInt 4 (mem_mul hpis hpis))
  have hk2 := mem_mulInt 8 (mem_mul hpis hpiy)
  have hgbh2 := mem_mul hQH (mem_add (mem_mul hk1 hC') (mem_mul hk2 hS'))
  have := mem_mul hp.hC (mem_add hgb2 hgbh2)
  have e : c * (gb2 a s y + gbh2 a s y) = c * (
      (((4 : ℤ) * (π * a * (π * a) * ((y - s) * (y - s))) - (2 : ℤ) * (π * a)) * Real.exp (-π * a * (y - s) ^ 2) +
       ((4 : ℤ) * (π * a * (π * a) * ((y + s) * (y + s))) - (2 : ℤ) * (π * a)) * Real.exp (-π * a * (y + s) ^ 2)) +
      2 / Real.sqrt a * Real.exp (-π * y ^ 2 / a) *
        ((((4 : ℤ) * (π * (y * (1 / a)) * (π * (y * (1 / a)))) - (2 : ℤ) * (π * (1 / a))) -
            (4 : ℤ) * (π * s * (π * s))) * Real.cos (2 * π * s * y) +
          (8 : ℤ) * (π * s * (π * (y * (1 / a)))) * Real.sin (2 * π * s * y))) := by
    unfold gb2 gbh2; push_cast; ring
  rw [e]; exact this

end terms

theorem gsum_cons (q : ℝ × ℝ × ℝ) (L : List (ℝ × ℝ × ℝ)) (x : ℝ) :
    gsum (q :: L) x = q.2.2 * (gb q.1 q.2.1 x + gbh q.1 q.2.1 x) + gsum L x := by
  obtain ⟨a, s, c⟩ := q; rfl

theorem gsum1_cons (q : ℝ × ℝ × ℝ) (L : List (ℝ × ℝ × ℝ)) (x : ℝ) :
    gsum1 (q :: L) x = q.2.2 * (gb1 q.1 q.2.1 x + gbh1 q.1 q.2.1 x) + gsum1 L x := by
  obtain ⟨a, s, c⟩ := q; rfl

theorem gsum2_cons (q : ℝ × ℝ × ℝ) (L : List (ℝ × ℝ × ℝ)) (x : ℝ) :
    gsum2 (q :: L) x = q.2.2 * (gb2 q.1 q.2.1 x + gbh2 q.1 q.2.1 x) + gsum2 L x := by
  obtain ⟨a, s, c⟩ := q; rfl

theorem mem_sum01 {P n k : ℕ} {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ {data : List GT} {pts : List PT}, List.Forall₂ (PTOk P) data pts → ∀ {G0 G1 : Ball},
      sum01 P n k Y pts = some (G0, G1) →
      mem P (gsum (data.map GT.toReal) y) G0 ∧ mem P (gsum1 (data.map GT.toReal) y) G1
  | _, _, List.Forall₂.nil, G0, G1, h => by
    simp only [sum01, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [gsum, gsum1, mem]
  | t :: data, p :: pts, List.Forall₂.cons htp hrest, G0, G1, h => by
    simp only [sum01, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨u, v⟩, hab, ⟨u', v'⟩, hcd, rfl, rfl⟩ := h
    have h1 := mem_term01 htp hY hab
    have h2 := mem_sum01 hY hrest hcd
    simp only [List.map_cons, gsum_cons, gsum1_cons]
    exact ⟨mem_add h1.1 h2.1, mem_add h1.2 h2.2⟩

theorem mem_sum2 {P n k : ℕ} {y : ℝ} {Y : Ball} (hY : mem P y Y) :
    ∀ {data : List GT} {pts : List PT}, List.Forall₂ (PTOk P) data pts → ∀ {G2 : Ball},
      sum2 P n k Y pts = some G2 → mem P (gsum2 (data.map GT.toReal) y) G2
  | _, _, List.Forall₂.nil, G2, h => by
    simp only [sum2, Option.some.injEq] at h
    subst h
    simp [gsum2, mem]
  | t :: data, p :: pts, List.Forall₂.cons htp hrest, G2, h => by
    simp only [sum2, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨u, hab, u', hcd, rfl⟩ := h
    simp only [List.map_cons, gsum2_cons]
    exact mem_add (mem_term2 htp hY hab) (mem_sum2 hY hrest hcd)

theorem forall₂_pos {P : ℕ} : ∀ {data : List GT} {pts : List PT}, List.Forall₂ (PTOk P) data pts →
    ∀ q ∈ data.map GT.toReal, 0 < q.1
  | _, _, List.Forall₂.nil => by simp
  | t :: data, p :: pts, List.Forall₂.cons htp hrest => by
    intro q hq
    simp only [List.map_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact htp.ha
    · exact forall₂_pos hrest q hq

theorem mem_point (P : ℕ) (y0 : ℤ) : mem P ((y0 : ℝ) / 2 ^ P) (⟨y0, 0⟩ : Ball) := by
  simp [mem]

theorem mem_center {P : ℕ} {y0 : ℤ} {η : ℕ} {x : ℝ}
    (hx : |x - (y0 : ℝ) / 2 ^ P| ≤ (η : ℝ) / 2 ^ P) : mem P x (⟨y0, η⟩ : Ball) := hx

theorem concave_pos {A B M el t : ℝ} (hA : 0 < A) (hM : 0 ≤ M) (ht0 : 0 ≤ t) (htel : t ≤ el)
    (hQ : 0 < A + B * el - M * el ^ 2 / 2) : 0 < A + B * t - M * t ^ 2 / 2 := by
  rcases eq_or_lt_of_le (ht0.trans htel) with hel | hel
  · have : t = 0 := by linarith
    subst this; simpa using hA
  · have key : el * (A + B * t - M * t ^ 2 / 2) =
        (el - t) * A + t * (A + B * el - M * el ^ 2 / 2) + M / 2 * t * (el - t) * el := by ring
    have h1 : 0 ≤ (el - t) * A := mul_nonneg (by linarith) hA.le
    have h2 : 0 ≤ t * (A + B * el - M * el ^ 2 / 2) := mul_nonneg ht0 hQ.le
    have h3 : 0 ≤ M / 2 * t * (el - t) * el := by
      have := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : 0 ≤ M / 2) ht0) (by linarith : 0 ≤ el - t)) hel.le
      exact this
    have h4 : 0 < (el - t) * A + t * (A + B * el - M * el ^ 2 / 2) := by
      rcases eq_or_lt_of_le ht0 with ht | ht
      · subst ht; simp; exact mul_pos hel hA
      · linarith [mul_pos ht hQ]
    have : 0 < el * (A + B * t - M * t ^ 2 / 2) := by rw [key]; linarith
    exact pos_of_mul_pos_right this hel.le

theorem ivOK_sound {P n k : ℕ} {data : List GT} {pts : List PT} (hF : List.Forall₂ (PTOk P) data pts)
    {lo hi : ℤ} (h : ivOK P n k pts lo hi = true) :
    ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) ((hi : ℝ) / 2 ^ P), 0 < gsum (data.map GT.toReal) y := by
  intro y hy
  have hP := two_pow_pos' P
  have hlohi : (lo : ℝ) ≤ hi := by
    have := hy.1.trans hy.2
    rwa [div_le_div_iff_of_pos_right hP] at this
  have hlohi' : lo ≤ hi := by exact_mod_cast hlohi
  unfold ivOK at h
  simp only at h
  set y0 : ℤ := (lo + hi) / 2 with hy0
  set η : ℕ := (max (y0 - lo) (hi - y0)).toNat with hη
  set L := data.map GT.toReal
  have hL := forall₂_pos hF
  have hmax : max (y0 - lo) (hi - y0) ≤ (η : ℤ) := Int.self_le_toNat _
  have h1 : y0 - lo ≤ (η : ℤ) := (le_max_left _ _).trans hmax
  have h2' : hi - y0 ≤ (η : ℤ) := (le_max_right _ _).trans hmax
  have h1r : ((y0 : ℝ) - lo) ≤ η := by exact_mod_cast h1
  have h2r : ((hi : ℝ) - y0) ≤ η := by exact_mod_cast h2'
  set e : ℝ := (η : ℝ) / 2 ^ P with he
  set c0 : ℝ := (y0 : ℝ) / 2 ^ P with hc0
  have he0 : 0 ≤ e := by positivity
  have hloc : (lo : ℝ) / 2 ^ P ≥ c0 - e := by
    rw [hc0, he, ← sub_div, ge_iff_le, div_le_div_iff_of_pos_right hP]; linarith
  have hhic : (hi : ℝ) / 2 ^ P ≤ c0 + e := by
    rw [hc0, he, ← add_div, div_le_div_iff_of_pos_right hP]; linarith
  cases h2 : sum2 P n k ⟨y0, η⟩ pts with
  | none => simp [h2] at h
  | some G2 =>
    have hM : ∀ x ∈ Set.Icc (c0 - e) (c0 + e), |gsum2 L x| ≤ (G2.absHi : ℝ) / 2 ^ P := by
      intro x hx
      have hxm : mem P x (⟨y0, η⟩ : Ball) := by
        apply mem_center
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      exact abs_le_absHi (mem_sum2 hxm hF h2)
    have hM0 : (0 : ℝ) ≤ (G2.absHi : ℝ) / 2 ^ P := by positivity
    simp only [h2, Bool.or_eq_true] at h
    rcases h with hc | hl
    · -- centred test
      cases h01 : sum01 P n k ⟨y0, 0⟩ pts with
      | none => simp [h01] at hc
      | some G01 =>
        obtain ⟨G0, G1⟩ := G01
        simp only [h01, decide_eq_true_eq] at hc
        obtain ⟨hg0, hg1⟩ := mem_sum01 (mem_point P y0) hF h01
        have hyI : y ∈ Set.Icc (c0 - e) (c0 + e) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have hT := taylor2_lower (hasDerivAt_gsum L) (hasDerivAt_gsum1 L hL) he0 hM y hyI
        have hv0 : ((G0.m : ℝ) - G0.r) / 2 ^ P ≤ gsum L c0 := by
          unfold mem at hg0
          have := (abs_le.mp hg0).1
          rw [sub_div]; linarith
        have hv1 : |gsum1 L c0| ≤ (G1.absHi : ℝ) / 2 ^ P := abs_le_absHi hg1
        have hdec : (0 : ℝ) < 2 * ((G0.m : ℝ) - G0.r) * (2 ^ P) ^ 2
            - 2 * (G1.absHi : ℝ) * η * 2 ^ P - (G2.absHi : ℝ) * η * η := by
          have hc' : ((0 : ℤ) : ℝ) < ((2 * (G0.m - (G0.r : ℤ)) * ((2 ^ (2 * P) : ℕ) : ℤ)
              - ((2 * G1.absHi * η * 2 ^ P : ℕ) : ℤ) - ((G2.absHi * η * η : ℕ) : ℤ) : ℤ) : ℝ) := by
            exact_mod_cast hc
          push_cast at hc'
          rw [show (2 : ℝ) ^ (2 * P) = (2 ^ P) ^ 2 by rw [← pow_mul, mul_comm]] at hc'
          linarith
        have key : 0 < ((G0.m : ℝ) - G0.r) / 2 ^ P - (G1.absHi : ℝ) / 2 ^ P * e
            - (G2.absHi : ℝ) / 2 ^ P * e ^ 2 / 2 := by
          have e1 : ((G0.m : ℝ) - G0.r) / 2 ^ P - (G1.absHi : ℝ) / 2 ^ P * e
              - (G2.absHi : ℝ) / 2 ^ P * e ^ 2 / 2 =
              (2 * ((G0.m : ℝ) - G0.r) * (2 ^ P) ^ 2 - 2 * (G1.absHi : ℝ) * η * 2 ^ P
                - (G2.absHi : ℝ) * η * η) / (2 * (2 ^ P) ^ 3) := by
            rw [he]; field_simp
          rw [e1]; exact div_pos hdec (by positivity)
        have hprod : |gsum1 L c0| * e ≤ (G1.absHi : ℝ) / 2 ^ P * e := mul_le_mul_of_nonneg_right hv1 he0
        linarith
    · -- left-anchored test
      cases h01 : sum01 P n k ⟨lo, 0⟩ pts with
      | none => simp [h01] at hl
      | some G01 =>
        obtain ⟨G0, G1⟩ := G01
        simp only [h01, Bool.and_eq_true, decide_eq_true_eq] at hl
        obtain ⟨hA, hQ⟩ := hl
        obtain ⟨hg0, hg1⟩ := mem_sum01 (mem_point P lo) hF h01
        have hhn : (((hi - lo).toNat : ℕ) : ℤ) = hi - lo := Int.toNat_of_nonneg (sub_nonneg.mpr hlohi')
        have hhr : (((hi - lo).toNat : ℕ) : ℝ) = (hi : ℝ) - lo := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hhn
          push_cast at this ⊢; linarith
        set cl : ℝ := (lo : ℝ) / 2 ^ P with hcl
        set el : ℝ := (((hi - lo).toNat : ℕ) : ℝ) / 2 ^ P with hel
        have hclel : cl + el = (hi : ℝ) / 2 ^ P := by rw [hcl, hel, hhr, ← add_div]; ring_nf
        have hM' : ∀ x ∈ Set.Icc cl (cl + el), |gsum2 L x| ≤ (G2.absHi : ℝ) / 2 ^ P := by
          intro x hx
          rw [hclel] at hx
          exact hM x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hyI : y ∈ Set.Icc cl (cl + el) := ⟨hy.1, by rw [hclel]; exact hy.2⟩
        have hT := taylor2_lower_right (hasDerivAt_gsum L) (hasDerivAt_gsum1 L hL) hM' y hyI
        have hv0 : ((G0.m : ℝ) - G0.r) / 2 ^ P ≤ gsum L cl := by
          unfold mem at hg0
          have := (abs_le.mp hg0).1
          rw [sub_div]; linarith
        have hv1 : ((G1.m : ℝ) - G1.r) / 2 ^ P ≤ gsum1 L cl := by
          unfold mem at hg1
          have := (abs_le.mp hg1).1
          rw [sub_div]; linarith
        set t := y - cl with ht
        have ht0 : 0 ≤ t := by linarith [hyI.1]
        have htel : t ≤ el := by linarith [hyI.2]
        have hAr : 0 < ((G0.m : ℝ) - G0.r) / 2 ^ P := by
          apply div_pos _ hP
          have : ((0 : ℤ) : ℝ) < ((G0.m - (G0.r : ℤ) : ℤ) : ℝ) := by exact_mod_cast hA
          push_cast at this; linarith
        have hQr : 0 < ((G0.m : ℝ) - G0.r) / 2 ^ P + ((G1.m : ℝ) - G1.r) / 2 ^ P * el
            - (G2.absHi : ℝ) / 2 ^ P * el ^ 2 / 2 := by
          have hq' : ((0 : ℤ) : ℝ) < ((2 * (G0.m - (G0.r : ℤ)) * ((2 ^ (2 * P) : ℕ) : ℤ)
              + 2 * (G1.m - (G1.r : ℤ)) * (((hi - lo).toNat : ℕ) : ℤ) * ((2 ^ P : ℕ) : ℤ)
              - ((G2.absHi * (hi - lo).toNat * (hi - lo).toNat : ℕ) : ℤ) : ℤ) : ℝ) := by
            exact_mod_cast hQ
          push_cast at hq'
          rw [show (2 : ℝ) ^ (2 * P) = (2 ^ P) ^ 2 by rw [← pow_mul, mul_comm]] at hq'
          have e1 : ((G0.m : ℝ) - G0.r) / 2 ^ P + ((G1.m : ℝ) - G1.r) / 2 ^ P * el
              - (G2.absHi : ℝ) / 2 ^ P * el ^ 2 / 2 =
              (2 * ((G0.m : ℝ) - G0.r) * (2 ^ P) ^ 2 + 2 * ((G1.m : ℝ) - G1.r) * ((hi - lo).toNat : ℝ) * 2 ^ P
                - (G2.absHi : ℝ) * ((hi - lo).toNat : ℝ) * ((hi - lo).toNat : ℝ)) / (2 * (2 ^ P) ^ 3) := by
            rw [hel]; field_simp
          rw [e1]; exact div_pos (by linarith) (by positivity)
        have hpos := concave_pos hAr hM0 ht0 htel hQr
        have hlin : ((G1.m : ℝ) - G1.r) / 2 ^ P * t ≤ gsum1 L cl * t := mul_le_mul_of_nonneg_right hv1 ht0
        have : gsum L cl + gsum1 L cl * (y - cl) - (G2.absHi : ℝ) / 2 ^ P * (y - cl) ^ 2 / 2 ≤ gsum L y := hT
        rw [← ht] at this
        linarith

theorem rangeOK_sound {P n k : ℕ} {data : List GT} {pts : List PT} (hF : List.Forall₂ (PTOk P) data pts) :
    ∀ (d : ℕ) (lo hi : ℤ), rangeOK P n k pts d lo hi = true →
      ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) ((hi : ℝ) / 2 ^ P), 0 < gsum (data.map GT.toReal) y := by
  intro d
  induction d with
  | zero => intro lo hi h; exact ivOK_sound hF h
  | succ d ih =>
    intro lo hi h y hy
    simp only [rangeOK, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ivOK_sound hF h y hy
    · rcases le_total y ((((lo + hi) / 2 : ℤ) : ℝ) / 2 ^ P) with hle | hle
      · exact ih lo _ h1 y ⟨hy.1, hle⟩
      · exact ih _ hi h2 y ⟨hle, hy.2⟩

theorem piecesOK_sound {P n k : ℕ} {data : List GT} {pts : List PT} (hF : List.Forall₂ (PTOk P) data pts)
    (d : ℕ) {w : ℤ} (hw : 0 ≤ w) :
    ∀ (c : ℕ) (lo : ℤ), piecesOK P n k pts d w c lo = true → 0 < c →
      ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) (((lo + c * w : ℤ) : ℝ) / 2 ^ P), 0 < gsum (data.map GT.toReal) y := by
  intro c
  induction c with
  | zero => intro lo _ hc; exact absurd hc (lt_irrefl 0)
  | succ c ih =>
    intro lo h _ y hy
    simp only [piecesOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hP := two_pow_pos' P
    rcases le_or_gt y (((lo + w : ℤ) : ℝ) / 2 ^ P) with hle | hgt
    · exact rangeOK_sound hF d lo (lo + w) h1 y ⟨hy.1, hle⟩
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

theorem tailSum_cons (aT sT Y : ℝ) (q : ℝ × ℝ × ℝ) (L : List (ℝ × ℝ × ℝ)) :
    tailSum aT sT Y (q :: L) = |q.2.2| * Rpair aT sT Y q.1 q.2.1 + tailSum aT sT Y L := by
  obtain ⟨a, s, c⟩ := q; rfl

section tail

variable {P n : ℕ} {tT : GT} {T : PT} {Yv : ℝ} {YB : Ball}

theorem mem_tailBase (hT : PTOk P tT T) (hY : mem P Yv YB) :
    mem P (π * tT.toReal.1 * (Yv - tT.toReal.2.1) ^ 2) (tailBase P T YB) := by
  have := mem_mul (mem_mul (mem_piB P) hT.hA) (mem_mul (mem_sub hY hT.hS) (mem_sub hY hT.hS))
  simp only [GT.toReal]
  rw [show π * ((tT.an : ℝ) / tT.ad) * (Yv - (tT.sn : ℝ) / tT.sd) ^ 2 =
    π * ((tT.an : ℝ) / tT.ad) * ((Yv - (tT.sn : ℝ) / tT.sd) * (Yv - (tT.sn : ℝ) / tT.sd)) by ring]
  exact this

theorem pairCondB_sound {t : GT} {p : PT} (hT : PTOk P tT T) (hp : PTOk P t p) (hY : mem P Yv YB)
    (h : pairCondB P T YB p = true) :
    PairCond tT.toReal.1 tT.toReal.2.1 Yv t.toReal.1 t.toReal.2.1 := by
  simp only [pairCondB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have g1 := isPos_sound (mem_sub hp.hA hT.hA) h1
  have g2 := isPos_sound (mem_sub (mem_mul (mem_sub hp.hA hT.hA) hY)
    (mem_sub (mem_mul hp.hA hp.hS) (mem_mul hT.hA hT.hS))) h2
  have g3 := isPos_sound (mem_sub (mem_mul (mem_sub hp.hA hT.hA) hY)
    (mem_sub (mem_neg (mem_mul hp.hA hp.hS)) (mem_mul hT.hA hT.hS))) h3
  have g4 := isPos_sound (mem_sub hp.hAi hT.hA) h4
  have g5 := isPos_sound (mem_sub (mem_mul (mem_sub hp.hAi hT.hA) hY) (mem_neg (mem_mul hT.hA hT.hS))) h5
  simp only [GT.toReal]
  refine ⟨hp.ha, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem mem_rpairB {t : GT} {p : PT} (hT : PTOk P tT T) (hp : PTOk P t p) (hY : mem P Yv YB) {R : Ball}
    (h : rpairB P n T YB p = some R) :
    mem P (Rpair tT.toReal.1 tT.toReal.2.1 Yv t.toReal.1 t.toReal.2.1) R := by
  simp only [rpairB, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨e1, he1, e2, he2, e3, he3, rfl⟩ := h
  have hb := mem_tailBase hT hY
  have hpi := mem_piB P
  have m1 := mem_expB' (mem_add (mem_neg (mem_mul (mem_mul hpi hp.hA) (mem_mul (mem_sub hY hp.hS)
    (mem_sub hY hp.hS)))) hb) he1
  have m2 := mem_expB' (mem_add (mem_neg (mem_mul (mem_mul hpi hp.hA) (mem_mul (mem_add hY hp.hS)
    (mem_add hY hp.hS)))) hb) he2
  have m3 := mem_expB' (mem_add (mem_neg (mem_mul (mem_mul hpi hp.hAi) (mem_mul hY hY))) hb) he3
  have := mem_add (mem_add m1 m2) (mem_mul hp.hQ m3)
  unfold Rpair
  simp only [GT.toReal] at this ⊢
  convert this using 3 <;> ring_nf

theorem tailSumB_sound (hT : PTOk P tT T) (hY : mem P Yv YB) :
    ∀ {ts : List GT} {ps : List PT}, List.Forall₂ (PTOk P) ts ps → ∀ {S : Ball},
      tailSumB P n T YB ps = some S →
      mem P (tailSum tT.toReal.1 tT.toReal.2.1 Yv (ts.map GT.toReal)) S ∧
      ∀ q ∈ ts.map GT.toReal, PairCond tT.toReal.1 tT.toReal.2.1 Yv q.1 q.2.1
  | _, _, List.Forall₂.nil, S, h => by
    simp only [tailSumB, Option.some.injEq] at h
    subst h
    simp [tailSum, mem]
  | t :: ts, p :: ps, List.Forall₂.cons htp hrest, S, h => by
    unfold tailSumB at h
    split_ifs at h with hc
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨R, hR, S', hS', rfl⟩ := h
    obtain ⟨m1, c1⟩ := tailSumB_sound hT hY hrest hS'
    have hpc := pairCondB_sound hT htp hY hc
    have mR := mem_rpairB hT htp hY hR
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, tailSum_cons]
      exact mem_add (mem_mul (mem_absB htp.hC) mR) m1
    · intro q hq
      simp only [List.map_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hpc
      · exact c1 q hq

theorem tailOK_sound {ts : List GT} {ps : List PT} (hT : PTOk P tT T) (hF : List.Forall₂ (PTOk P) ts ps)
    (hY : mem P Yv YB) (h : tailOK P n T ps YB = true) :
    0 < tT.toReal.2.2 ∧ tT.toReal.1 ≤ 1 / tT.toReal.1 ∧
    1 / tT.toReal.1 * 0 - tT.toReal.1 * tT.toReal.2.1 ≤ (1 / tT.toReal.1 - tT.toReal.1) * Yv ∧
    (∀ q ∈ ts.map GT.toReal, PairCond tT.toReal.1 tT.toReal.2.1 Yv q.1 q.2.1) ∧
    0 < tT.toReal.2.2 - tT.toReal.2.2 * RT tT.toReal.1 tT.toReal.2.1 Yv -
      tailSum tT.toReal.1 tT.toReal.2.1 Yv (ts.map GT.toReal) := by
  unfold tailOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have g1 := isPos_sound hT.hC h1
  have g2 := isPos_sound (mem_sub hT.hAi hT.hA) h2
  have g3 := isPos_sound (mem_sub (mem_mul (mem_sub hT.hAi hT.hA) hY) (mem_neg (mem_mul hT.hA hT.hS))) h3
  split at h4
  · rename_i e3 S he3 hS
    obtain ⟨mS, cS⟩ := tailSumB_sound hT hY hF hS
    have hb := mem_tailBase hT hY
    have m3 := mem_expB' (mem_add (mem_neg (mem_mul (mem_mul (mem_piB P) hT.hAi) (mem_mul hY hY))) hb) he3
    have hRT : mem P (RT tT.toReal.1 tT.toReal.2.1 Yv) (mul P T.Q e3) := by
      have := mem_mul hT.hQ m3
      unfold RT
      simp only [GT.toReal] at this ⊢
      convert this using 3; ring_nf
    have g4 := isPos_sound (mem_sub (mem_sub hT.hC (mem_mul hT.hC hRT)) mS) h4
    simp only [GT.toReal] at g1 g2 g3 g4 ⊢
    refine ⟨g1, by linarith, by linarith, cS, by linarith⟩
  · exact absurd h4 (by simp)

end tail

theorem checkUpper_sound (c : Cfg) (data : List GT) (h : checkUpper c data = true) :
    (∀ q ∈ data.map GT.toReal, 0 < q.1) ∧ gsum (data.map GT.toReal) 0 < 0 ∧
      ∀ y, (c.rn : ℝ) / c.rd ≤ y → 0 < gsum (data.map GT.toReal) y := by
  unfold checkUpper at h
  cases hp : prepAll c.P data with
  | none => simp [hp] at h
  | some pts =>
    cases pts with
    | nil => simp [hp] at h
    | cons T R =>
      simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hpos, hcov⟩, hg0⟩, htail⟩, hpieces⟩ := h
      obtain ⟨hrn, hrd, hYd, hw, hcnt⟩ := hpos
      have hF := prepAll_ok hp
      have hL := forall₂_pos hF
      have hP := two_pow_pos' c.P
      refine ⟨hL, ?_, ?_⟩
      · -- g(0) < 0
        split at hg0
        · rename_i G0 G1 h01
          have := (mem_sum01 (mem_point c.P 0) hF h01).1
          simp only [Int.cast_zero, zero_div] at this
          exact isNeg_sound this hg0
        · exact absurd hg0 (by simp)
      · -- positivity on [r, ∞)
        cases hF with
        | cons hT hR =>
          rename_i tT ts
          have hYB := mem_ofRat c.P (c.Yn : ℤ) c.Yd hYd
          simp only [Int.cast_natCast] at hYB
          obtain ⟨tc1, tc2, tc3, tc4, tc5⟩ := tailOK_sound hT hR hYB htail
          have htailpos := tail_pos (R := ts.map GT.toReal) (Y := (c.Yn : ℝ) / c.Yd)
            (by have := hT.ha; simpa [GT.toReal] using this) tc1 tc2 tc3 tc4 tc5
          have hpc := piecesOK_sound (hF := List.Forall₂.cons hT hR) c.depth (w := (c.w : ℤ))
            (by positivity) c.cnt _ hpieces hcnt
          intro y hy
          have hrdr : (0 : ℝ) < c.rd := by exact_mod_cast hrd
          have hYdr : (0 : ℝ) < c.Yd := by exact_mod_cast hYd
          rcases le_or_gt y ((c.Yn : ℝ) / c.Yd) with hyY | hyY
          · apply hpc
            constructor
            · -- lo0 / 2^P ≤ r ≤ y
              have h1 : ((c.rn * 2 ^ c.P / c.rd : ℕ) : ℝ) * c.rd ≤ c.rn * 2 ^ c.P := by
                exact_mod_cast Nat.div_mul_le_self (c.rn * 2 ^ c.P) c.rd
              have h2 : ((c.rn * 2 ^ c.P / c.rd : ℕ) : ℝ) / 2 ^ c.P ≤ (c.rn : ℝ) / c.rd := by
                rw [div_le_div_iff₀ hP hrdr]; linarith
              simp only [Int.cast_natCast]
              linarith
            · -- y ≤ Y ≤ hi / 2^P
              have h3 : ((c.Yn * 2 ^ c.P : ℕ) : ℝ) ≤ (((c.rn * 2 ^ c.P / c.rd + c.cnt * c.w) * c.Yd : ℕ) : ℝ) := by
                exact_mod_cast hcov
              push_cast at h3
              have h4 : (c.Yn : ℝ) / c.Yd ≤ (((c.rn * 2 ^ c.P / c.rd : ℕ) : ℝ) + c.cnt * c.w) / 2 ^ c.P := by
                rw [div_le_div_iff₀ hYdr hP]; linarith
              simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
              linarith
          · have := htailpos y hyY.le
            simpa [GT.toReal] using this

theorem contig_sound {P n k : ℕ} {data : List GT} {pts : List PT} (hF : List.Forall₂ (PTOk P) data pts)
    (d : ℕ) : ∀ (segs : List Seg) (lo e : ℤ), contigEnd lo segs = some e →
      (∀ s ∈ segs, piecesOK P n k pts d s.w s.m s.lo = true) → segs ≠ [] →
      ∀ y ∈ Set.Icc ((lo : ℝ) / 2 ^ P) ((e : ℝ) / 2 ^ P), 0 < gsum (data.map GT.toReal) y := by
  intro segs
  induction segs with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons s ss ih =>
    intro lo e hc hall _ y hy
    simp only [contigEnd] at hc
    split_ifs at hc with hcond
    obtain ⟨hlo, hm, hw⟩ := hcond
    have hs := hall s (by simp)
    have hpc := piecesOK_sound hF d (w := (s.w : ℤ)) (by positivity) s.m s.lo hs hm
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

theorem upper_sharded_sound (c : Cfg) (data : List GT) (segs : List Seg) (hb : baseOK c data segs = true)
    (hs : List.Forall (fun s => segOK c data s = true) segs) :
    (∀ q ∈ data.map GT.toReal, 0 < q.1) ∧ gsum (data.map GT.toReal) 0 < 0 ∧
      ∀ y, (c.rn : ℝ) / c.rd ≤ y → 0 < gsum (data.map GT.toReal) y := by
  unfold baseOK at hb
  cases hp : prepAll c.P data with
  | none => simp [hp] at hb
  | some pts =>
    cases pts with
    | nil => simp [hp] at hb
    | cons T R =>
      simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨hpos, hcov⟩, hg0⟩, htail⟩ := hb
      obtain ⟨hrn, hrd, hYd, hne⟩ := hpos
      have hF := prepAll_ok hp
      have hL := forall₂_pos hF
      have hP := two_pow_pos' c.P
      have hall : ∀ s ∈ segs, piecesOK c.P c.n c.k (T :: R) c.depth s.w s.m s.lo = true := by
        intro s hsm
        have := List.forall_iff_forall_mem.mp hs s hsm
        simpa [segOK, hp] using this
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
          have hrange := contig_sound hF c.depth segs _ e he hall hne
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
            · apply hrange
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

end SignUnc.Chk
