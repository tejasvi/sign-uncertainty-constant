import Mathlib
import SUCert.Jet

/-!
# Soundness of the integer polynomial positivity test of checker v4 (`tshift`, `nodeOK`, `polyOK`)

`peval cs x = Σ_i cs_i x^i`.  `tshift s cs` represents `p(x + s)`; `lowB` is a lower bound on `[-1, 1]`;
`polyOK m b K fuel d n0` gives `K < Σ_j b_j σ^j` for `σ ∈ [(n0 - 1)/2^d, (n0 + 1)/2^d]`.
-/

namespace SignUnc.Chk

open Finset

/-- `Σ_i cs_i x^i` (Horner form). -/
def peval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * peval cs x

@[simp] theorem peval_nil (x : ℝ) : peval [] x = 0 := rfl
@[simp] theorem peval_cons (c : ℤ) (cs : List ℤ) (x : ℝ) : peval (c :: cs) x = c + x * peval cs x := rfl

theorem peval_zipWith_add : ∀ (a b : List ℤ), a.length = b.length → ∀ x,
    peval (List.zipWith (· + ·) a b) x = peval a x + peval b x
  | [], [], _, x => by simp
  | a :: as, b :: bs, h, x => by
    simp only [List.zipWith_cons_cons, peval_cons, Int.cast_add]
    rw [peval_zipWith_add as bs (by simpa using h) x]; ring
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem peval_map_mul (s : ℤ) : ∀ (a : List ℤ) (x : ℝ), peval (a.map (s * ·)) x = s * peval a x
  | [], x => by simp
  | a :: as, x => by
    simp only [List.map_cons, peval_cons, Int.cast_mul]
    rw [peval_map_mul s as x]; ring

theorem peval_append_zero : ∀ (a : List ℤ) (x : ℝ), peval (a ++ [0]) x = peval a x
  | [], x => by simp
  | a :: as, x => by simp only [List.cons_append, peval_cons]; rw [peval_append_zero as x]

theorem tshift_length (s : ℤ) : ∀ cs : List ℤ, (tshift s cs).length = cs.length
  | [] => rfl
  | c :: cs => by
    simp only [tshift, List.length_zipWith, List.length_cons, List.length_append, List.length_map,
      tshift_length s cs]
    omega

/-- `tshift s cs` represents `p(x + s)`. -/
theorem peval_tshift (s : ℤ) : ∀ (cs : List ℤ) (x : ℝ), peval (tshift s cs) x = peval cs (x + s)
  | [], x => by simp [tshift]
  | c :: cs, x => by
    simp only [tshift]
    rw [peval_zipWith_add _ _ (by simp [tshift_length])]
    rw [peval_cons, peval_append_zero, peval_map_mul, peval_tshift s cs x, peval_cons]
    ring

/-- `|p(x)| ≤ Σ |cs_i|` for `|x| ≤ 1`. -/
theorem abs_peval_le : ∀ (cs : List ℤ) {x : ℝ}, |x| ≤ 1 → |peval cs x| ≤ (((cs.map Int.natAbs).sum : ℕ) : ℝ)
  | [], x, _ => by simp
  | c :: cs, x, hx => by
    simp only [peval_cons, List.map_cons, List.sum_cons, Nat.cast_add]
    have h1 := abs_peval_le cs hx
    have h2 : |x * peval cs x| ≤ |peval cs x| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hx
    have h3 : |(c : ℝ)| = ((c.natAbs : ℕ) : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    calc |(c : ℝ) + x * peval cs x| ≤ |(c : ℝ)| + |x * peval cs x| := abs_add_le _ _
      _ ≤ _ := by rw [h3]; linarith

/-- `lowB` is a lower bound of the polynomial on `[-1, 1]`. -/
theorem lowB_le : ∀ (cs : List ℤ) {x : ℝ}, |x| ≤ 1 → ((lowB cs : ℤ) : ℝ) ≤ peval cs x
  | [], x, _ => by simp [lowB]
  | c :: cs, x, hx => by
    simp only [lowB, peval_cons, Int.cast_sub, Int.cast_natCast]
    have h1 := abs_peval_le cs hx
    have h2 : |x * peval cs x| ≤ |peval cs x| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hx
    have h3 := neg_abs_le (x * peval cs x)
    linarith

/-- `scaleAux d e bs` has entries `b_j 2^(e - j d)`. -/
theorem peval_scaleAux (d : ℕ) : ∀ (bs : List ℤ) (e : ℕ) (x : ℝ),
    peval (scaleAux d e bs) x = ∑ j ∈ range bs.length, (bs.getD j 0 : ℝ) * 2 ^ (e - j * d) * x ^ j
  | [], e, x => by simp [scaleAux]
  | b :: bs, e, x => by
    simp only [scaleAux, peval_cons, List.length_cons]
    rw [peval_scaleAux d bs (e - d) x]
    rw [sum_range_succ', mul_sum]
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, zero_mul, Nat.sub_zero]
    push_cast
    rw [add_comm]
    congr 1
    refine sum_congr rfl (fun j hj => ?_)
    have hj' : j < bs.length := by simpa using hj
    have hexp : e - d - j * d = e - (j + 1) * d := by rw [Nat.sub_sub, add_mul, one_mul, add_comm d (j * d)]
    rw [hexp, pow_succ]; ring

/-- The polynomial of a node: `peval (scaleAux d (d m) b) (2^d σ) = 2^{dm} Σ_j b_j σ^j` (`b` of length `m + 1`). -/
theorem peval_scaleAux_node (m d : ℕ) (b : List ℤ) (hb : b.length = m + 1) (σ : ℝ) :
    peval (scaleAux d (d * m) b) (2 ^ d * σ) = 2 ^ (d * m) * peval b σ := by
  rw [peval_scaleAux d b (d * m)]
  -- right side as a sum
  have hpe : ∀ (l : List ℤ) (x : ℝ), peval l x = ∑ j ∈ range l.length, (l.getD j 0 : ℝ) * x ^ j := by
    intro l x
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [peval_cons, List.length_cons, ih]
      rw [sum_range_succ', mul_sum]
      simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
      rw [add_comm]; congr 1
      refine sum_congr rfl (fun j _ => ?_); ring
  rw [hpe, mul_sum, hb]
  refine sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ m := by simp at hj; omega
  have hsplit : (2 : ℝ) ^ (d * m) = 2 ^ (d * m - j * d) * 2 ^ (j * d) := by
    rw [← pow_add]; congr 1; have : j * d ≤ d * m := by nlinarith
    omega
  rw [hsplit, mul_pow, ← pow_mul, show d * j = j * d by ring]
  ring

/-- One node: `K < Σ_j b_j σ^j` for `σ ∈ [(n0-1)/2^d, (n0+1)/2^d]`. -/
theorem nodeOK_sound {m : ℕ} {b : List ℤ} (hb : b.length = m + 1) {K d : ℕ} {n0 : ℤ}
    (h : nodeOK m b K d n0 = true) {σ : ℝ} (hσ1 : ((n0 : ℝ) - 1) / 2 ^ d ≤ σ) (hσ2 : σ ≤ ((n0 : ℝ) + 1) / 2 ^ d) :
    (K : ℝ) < peval b σ := by
  unfold nodeOK at h
  have h' := of_decide_eq_true h
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  set ρ : ℝ := 2 ^ d * σ - n0 with hρ
  have hρ1 : |ρ| ≤ 1 := by
    rw [abs_le]; constructor
    · have := (div_le_iff₀ h2d).mp hσ1; rw [hρ]; linarith
    · have := (le_div_iff₀ h2d).mp hσ2; rw [hρ]; linarith
  have hlow := lowB_le (tshift n0 (scaleAux d (d * m) b)) hρ1
  rw [peval_tshift, show ρ + n0 = 2 ^ d * σ by rw [hρ]; ring, peval_scaleAux_node m d b hb σ] at hlow
  have hK : ((K * 2 ^ (d * m) : ℕ) : ℤ) < lowB (tshift n0 (scaleAux d (d * m) b)) := h'
  have hK' : ((K : ℝ) * 2 ^ (d * m)) < (lowB (tshift n0 (scaleAux d (d * m) b)) : ℝ) := by
    have := (Int.cast_lt (R := ℝ)).mpr hK
    push_cast at this; exact this
  have hpos : (0 : ℝ) < 2 ^ (d * m) := by positivity
  nlinarith

/-- Bisection. -/
theorem polyOK_sound {m : ℕ} {b : List ℤ} (hb : b.length = m + 1) {K : ℕ} :
    ∀ (fuel d : ℕ) (n0 : ℤ), polyOK m b K fuel d n0 = true → ∀ σ : ℝ,
      ((n0 : ℝ) - 1) / 2 ^ d ≤ σ → σ ≤ ((n0 : ℝ) + 1) / 2 ^ d → (K : ℝ) < peval b σ := by
  intro fuel
  induction fuel with
  | zero => intro d n0 h σ h1 h2; exact nodeOK_sound hb (by simpa [polyOK] using h) h1 h2
  | succ f ih =>
    intro d n0 h σ h1 h2
    simp only [polyOK, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hl, hr⟩
    · exact nodeOK_sound hb h h1 h2
    · have h2d : (0 : ℝ) < 2 ^ d := by positivity
      have e : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
      rcases le_total σ ((n0 : ℝ) / 2 ^ d) with hs | hs
      · refine ih (d + 1) (2 * n0 - 1) hl σ ?_ ?_
        · rw [e]; push_cast
          calc (2 * (n0 : ℝ) - 1 - 1) / (2 * 2 ^ d) = ((n0 : ℝ) - 1) / 2 ^ d := by field_simp; ring
            _ ≤ σ := h1
        · rw [e]; push_cast
          calc σ ≤ (n0 : ℝ) / 2 ^ d := hs
            _ = (2 * (n0 : ℝ) - 1 + 1) / (2 * 2 ^ d) := by field_simp; ring
      · refine ih (d + 1) (2 * n0 + 1) hr σ ?_ ?_
        · rw [e]; push_cast
          calc (2 * (n0 : ℝ) + 1 - 1) / (2 * 2 ^ d) = (n0 : ℝ) / 2 ^ d := by field_simp; ring
            _ ≤ σ := hs
        · rw [e]; push_cast
          calc σ ≤ ((n0 : ℝ) + 1) / 2 ^ d := h2
            _ = (2 * (n0 : ℝ) + 1 + 1) / (2 * 2 ^ d) := by field_simp; ring

/-- The top call `polyOK m b K fuel 0 0`: `K < Σ_j b_j σ^j` on `[-1, 1]`. -/
theorem polyOK_top {m : ℕ} {b : List ℤ} (hb : b.length = m + 1) {K fuel : ℕ} (h : polyOK m b K fuel 0 0 = true)
    {σ : ℝ} (hσ : |σ| ≤ 1) : (K : ℝ) < peval b σ := by
  rw [abs_le] at hσ
  exact polyOK_sound hb fuel 0 0 h σ (by simpa using hσ.1) (by simpa using hσ.2)

end SignUnc.Chk
