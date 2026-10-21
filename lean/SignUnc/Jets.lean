import Mathlib

/-!
# Taylor coefficients of quadratic exponentials

`ecoef α β j` are the Taylor coefficients of `exp(α t + β t²)` at `t = 0`, defined by the recurrence
`e_0 = 1`, `e_1 = α`, `(j+2) e_{j+2} = α e_{j+1} + 2β e_j`.  Main facts:
* `ecoef_add`: `e_j(α₁ + α₂) = Σ_{p ≤ j} e_{j-p}(α₁) α₂^p / p!`;
* `hasDerivAt_qexp`: for `q(y) = B y² + C y + D`, `y ↦ exp(q y) e_j(q'(y), B)` has derivative
  `(j+1) exp(q y) e_{j+1}(q'(y), B)`.
-/

open Finset

namespace SignUnc

/-- Taylor coefficients of `exp(α t + β t²)`. -/
def ecoef {K : Type*} [Field K] (α β : K) : ℕ → K
  | 0 => 1
  | 1 => α
  | j + 2 => (α * ecoef α β (j + 1) + 2 * β * ecoef α β j) / (j + 2)

section Basic
variable {K : Type*} [Field K]

@[simp] theorem ecoef_zero (α β : K) : ecoef α β 0 = 1 := rfl
@[simp] theorem ecoef_one (α β : K) : ecoef α β 1 = α := rfl
theorem ecoef_succ_succ (α β : K) (j : ℕ) :
    ecoef α β (j + 2) = (α * ecoef α β (j + 1) + 2 * β * ecoef α β j) / (j + 2) := rfl

theorem ecoef_map {L : Type*} [Field L] (f : K →+* L) (α β : K) (j : ℕ) :
    f (ecoef α β j) = ecoef (f α) (f β) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simp
    | 1 => simp
    | j + 2 =>
      rw [ecoef_succ_succ, ecoef_succ_succ]
      simp only [map_div₀, map_add, map_mul, map_natCast, map_ofNat, ih (j + 1) (by omega), ih j (by omega)]

end Basic

section Field
variable {K : Type*} [Field K] [CharZero K]

theorem ecoef_rec (α β : K) (j : ℕ) :
    ((j : K) + 2) * ecoef α β (j + 2) = α * ecoef α β (j + 1) + 2 * β * ecoef α β j := by
  rw [ecoef_succ_succ]
  have : (j : K) + 2 ≠ 0 := by norm_cast
  field_simp

/-- The right-hand side of `ecoef_add`. -/
def ecoefS (α₁ β α₂ : K) (j : ℕ) : K :=
  ∑ p ∈ range (j + 1), ecoef α₁ β (j - p) * α₂ ^ p / (p.factorial : K)

theorem ecoefS_rec (α₁ β α₂ : K) (j : ℕ) :
    ((j : K) + 2) * ecoefS α₁ β α₂ (j + 2) =
      (α₁ + α₂) * ecoefS α₁ β α₂ (j + 1) + 2 * β * ecoefS α₁ β α₂ j := by
  -- split (j+2) = (j+2-p) + p in every term
  have hsplit : ((j : K) + 2) * ecoefS α₁ β α₂ (j + 2) =
      (∑ p ∈ range (j + 3), (((j + 2 - p : ℕ) : K) * ecoef α₁ β (j + 2 - p)) * α₂ ^ p / (p.factorial : K)) +
      ∑ p ∈ range (j + 3), (p : K) * ecoef α₁ β (j + 2 - p) * α₂ ^ p / (p.factorial : K) := by
    unfold ecoefS
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun p hp => ?_)
    have hp' : p ≤ j + 2 := by simp at hp; omega
    have : ((j + 2 - p : ℕ) : K) = (j : K) + 2 - p := by push_cast [Nat.cast_sub hp']; ring
    rw [this]; ring
  -- first sum: the recurrence in every term
  have h1 : (∑ p ∈ range (j + 3), (((j + 2 - p : ℕ) : K) * ecoef α₁ β (j + 2 - p)) * α₂ ^ p / (p.factorial : K)) =
      α₁ * ecoefS α₁ β α₂ (j + 1) + 2 * β * ecoefS α₁ β α₂ j := by
    unfold ecoefS
    rw [sum_range_succ, sum_range_succ, sum_range_succ (fun p => ecoef α₁ β (j + 1 - p) * α₂ ^ p / (p.factorial : K))]
    have hl : j + 2 - (j + 2) = 0 := by omega
    have hm : j + 2 - (j + 1) = 1 := by omega
    have hn : j + 1 - (j + 1) = 0 := by omega
    rw [hl, hm, hn]
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, Nat.cast_one, one_mul, ecoef_one, ecoef_zero, mul_one]
    have core : (∑ p ∈ range (j + 1), (((j + 2 - p : ℕ) : K) * ecoef α₁ β (j + 2 - p)) * α₂ ^ p / (p.factorial : K)) =
        α₁ * (∑ p ∈ range (j + 1), ecoef α₁ β (j + 1 - p) * α₂ ^ p / (p.factorial : K)) +
        2 * β * (∑ p ∈ range (j + 1), ecoef α₁ β (j - p) * α₂ ^ p / (p.factorial : K)) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun p hp => ?_)
      have hp' : p ≤ j := by simp at hp; omega
      have e1 : j + 2 - p = (j - p) + 2 := by omega
      have e2 : j + 1 - p = (j - p) + 1 := by omega
      rw [e1, e2]
      have := ecoef_rec α₁ β (j - p)
      have hc : (((j - p + 2 : ℕ)) : K) = ((j - p : ℕ) : K) + 2 := by push_cast; ring
      rw [hc, this]; ring
    rw [core]; ring
  -- second sum: p / p! = 1 / (p-1)!
  have h2 : (∑ p ∈ range (j + 3), (p : K) * ecoef α₁ β (j + 2 - p) * α₂ ^ p / (p.factorial : K)) =
      α₂ * ecoefS α₁ β α₂ (j + 1) := by
    unfold ecoefS
    rw [sum_range_succ', mul_sum]
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    refine sum_congr rfl (fun p _ => ?_)
    rw [Nat.factorial_succ, show j + 2 - (p + 1) = j + 1 - p by omega]
    have hf : (p.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
    have hp1 : (p : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero p
    push_cast
    field_simp
    ring
  rw [hsplit, h1, h2]; ring

theorem ecoef_add (α₁ β α₂ : K) (j : ℕ) : ecoef (α₁ + α₂) β j = ecoefS α₁ β α₂ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simp [ecoefS]
    | 1 => simp [ecoefS, sum_range_succ]
    | j + 2 =>
      have hne : (j : K) + 2 ≠ 0 := by norm_cast
      have h := ecoefS_rec α₁ β α₂ j
      rw [← ih (j + 1) (by omega), ← ih j (by omega)] at h
      rw [ecoef_succ_succ, ← h]
      field_simp

end Field

/-! ## Derivatives -/

open Complex

/-- Along a path `α` with constant derivative `a'`, `e_{j+1}(α)` has derivative `e_j(α) a'`. -/
theorem hasDerivAt_ecoef_path (β : ℂ) {α : ℝ → ℂ} {a' : ℂ} (hα : ∀ y, HasDerivAt α a' y) :
    ∀ (j : ℕ) (y : ℝ), HasDerivAt (fun y => ecoef (α y) β (j + 1)) (ecoef (α y) β j * a') y := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro y
    match j with
    | 0 => simpa using hα y
    | 1 =>
      have h := (((hα y).mul (hα y)).add_const (2 * β * 1)).div_const 2
      have hfun : (fun y => ecoef (α y) β (1 + 1)) = fun y => (α y * α y + 2 * β * 1) / 2 := by
        funext y
        rw [show (1 + 1 : ℕ) = 0 + 2 from rfl, ecoef_succ_succ]
        simp
      rw [hfun]
      refine h.congr_deriv ?_
      simp only [ecoef_one]; ring
    | j + 2 =>
      have h1 := (hα y).mul (ih (j + 1) (by omega) y)
      have h2 := (ih j (by omega) y).const_mul (2 * β)
      have h := (h1.add h2).div_const ((j : ℂ) + 3)
      have hfun : (fun y => ecoef (α y) β (j + 2 + 1)) =
          fun y => (α y * ecoef (α y) β (j + 1 + 1) + 2 * β * ecoef (α y) β (j + 1)) / ((j : ℂ) + 3) := by
        funext y
        rw [show j + 2 + 1 = (j + 1) + 2 by omega, ecoef_succ_succ]
        congr 1; push_cast; ring
      rw [hfun]
      refine h.congr_deriv ?_
      have hr : ((j : ℂ) + 2) * ecoef (α y) β (j + 1 + 1) = α y * ecoef (α y) β (j + 1) + 2 * β * ecoef (α y) β j :=
        ecoef_rec (α y) β j
      have hne : (j : ℂ) + 3 ≠ 0 := by norm_cast
      rw [div_eq_iff hne]
      linear_combination (-a') * hr

/-- `y ↦ (y : ℂ)`. -/
theorem hasDerivAt_ofReal' (y : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
  simpa using (hasDerivAt_id y).ofReal_comp

/-- The quadratic exponential times `e_j(q')`: its derivative is `(j+1)` times the next one. -/
theorem hasDerivAt_qexp (B C D : ℂ) (j : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (B * (y : ℂ) ^ 2 + C * y + D) * ecoef (2 * B * y + C) B j)
      (((j : ℂ) + 1) * (Complex.exp (B * (y : ℂ) ^ 2 + C * y + D) * ecoef (2 * B * y + C) B (j + 1))) y := by
  have hy := hasDerivAt_ofReal' y
  have hq : HasDerivAt (fun y : ℝ => B * (y : ℂ) ^ 2 + C * y + D) (2 * B * y + C) y := by
    have := (((hy.pow 2).const_mul B).add (hy.const_mul C)).add_const D
    refine this.congr_deriv ?_
    simp; ring
  have hexp := hq.cexp
  have hα : ∀ y, HasDerivAt (fun y : ℝ => 2 * B * (y : ℂ) + C) (2 * B) y := fun y => by
    have := ((hasDerivAt_ofReal' y).const_mul (2 * B)).add_const C
    simpa using this
  match j with
  | 0 =>
    have := hexp.mul_const (1 : ℂ)
    simp only [ecoef_zero, mul_one] at this ⊢
    refine this.congr_deriv ?_
    simp
  | j + 1 =>
    have he := hasDerivAt_ecoef_path B hα j y
    have := hexp.mul he
    refine this.congr_deriv ?_
    have hr : ((j : ℂ) + 2) * ecoef (2 * B * (y : ℂ) + C) B (j + 1 + 1) =
        (2 * B * (y : ℂ) + C) * ecoef (2 * B * (y : ℂ) + C) B (j + 1) + 2 * B * ecoef (2 * B * (y : ℂ) + C) B j :=
      ecoef_rec (2 * B * (y : ℂ) + C) B j
    push_cast
    linear_combination (-Complex.exp (B * (y : ℂ) ^ 2 + C * y + D)) * hr

/-- Real parts. -/
theorem hasDerivAt_re_comp {f : ℝ → ℂ} {f' : ℂ} {y : ℝ} (h : HasDerivAt f f' y) :
    HasDerivAt (fun y => (f y).re) f'.re y := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h
  simpa [Function.comp_def] using this

/-- One term `Re(K exp(q y) e_j(q' y))` with `q y = B y² + C y + D`. -/
noncomputable def tau (K B C D : ℂ) (j : ℕ) (y : ℝ) : ℝ :=
  (K * (Complex.exp (B * (y : ℂ) ^ 2 + C * y + D) * ecoef (2 * B * y + C) B j)).re

theorem hasDerivAt_tau (K B C D : ℂ) (j : ℕ) (y : ℝ) :
    HasDerivAt (tau K B C D j) (((j : ℝ) + 1) * tau K B C D (j + 1) y) y := by
  have h := hasDerivAt_re_comp ((hasDerivAt_qexp B C D j y).const_mul K)
  refine h.congr_deriv ?_
  unfold tau
  rw [show K * (((j : ℂ) + 1) * (Complex.exp (B * (y : ℂ) ^ 2 + C * y + D) * ecoef (2 * B * y + C) B (j + 1))) =
    (((j : ℝ) + 1 : ℝ) : ℂ) * (K * (Complex.exp (B * (y : ℂ) ^ 2 + C * y + D) * ecoef (2 * B * y + C) B (j + 1))) by
    push_cast; ring]
  rw [Complex.re_ofReal_mul]

/-- A sum of terms. -/
noncomputable def tauSum (L : List (ℂ × ℂ × ℂ × ℂ)) (j : ℕ) (y : ℝ) : ℝ :=
  (L.map fun q => tau q.1 q.2.1 q.2.2.1 q.2.2.2 j y).sum

theorem hasDerivAt_tauSum (L : List (ℂ × ℂ × ℂ × ℂ)) (j : ℕ) (y : ℝ) :
    HasDerivAt (tauSum L j) (((j : ℝ) + 1) * tauSum L (j + 1) y) y := by
  induction L with
  | nil =>
    have e : tauSum [] j = fun _ => 0 := by funext y; simp [tauSum]
    rw [e]
    convert hasDerivAt_const y (0 : ℝ) using 1
    simp [tauSum]
  | cons q L ih =>
    have := (hasDerivAt_tau q.1 q.2.1 q.2.2.1 q.2.2.2 j y).add ih
    unfold tauSum at this ⊢
    simp only [List.map_cons, List.sum_cons]
    refine this.congr_deriv ?_
    ring

end SignUnc
