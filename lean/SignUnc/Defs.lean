import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Problem 6.11 (sign uncertainty, dimension one): statement

Fourier transform `f̂(ξ) = ∫ f(x) e^{-2πixξ} dx` (Mathlib's `𝓕`).  For `f : ℝ → ℂ`,
`A(f) = inf {r > 0 : f(x) is real and f(x) ≥ 0 for all |x| ≥ r}`, in `[0, ∞]` with `inf ∅ = ∞`.

`𝒜` is the set of nonzero even `f : ℝ → ℝ` with `f`, `f̂` integrable, `f(0) ≤ 0`, `f̂(0) ≤ 0`; as in the
paper, `f` is taken continuous (such `f` agree a.e. with a continuous function, and the paper always uses
that version).  `A₊(1)² = inf_{f ∈ 𝒜} A(f) A(f̂)` and `A₊(1)` is its square root.

The class of Problem 6.11: even integrable `f : ℝ → ℝ`, continuous at `0`, with `f(0) < 0` and
`f̂(0) < 0`; `C_{6.11} = inf A(f) A(f̂)` over it (the largest constant `C` with `A(f) A(f̂) ≥ C`).
-/

open MeasureTheory Set Complex Real
open scoped FourierTransform ENNReal

namespace SignUnc

/-- The Fourier transform of a real function, as a complex function. -/
noncomputable def ft (f : ℝ → ℝ) : ℝ → ℂ := 𝓕 (fun x => (f x : ℂ))

/-- `A(f) = inf {r > 0 : f(x) is real and ≥ 0 for all |x| ≥ r}` (`= ∞` if there is no such `r`). -/
noncomputable def A (f : ℝ → ℂ) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : 0 < r ∧ ∀ x : ℝ, r ≤ |x| → (f x).im = 0 ∧ 0 ≤ (f x).re), ENNReal.ofReal r

/-- The class `𝒜`. -/
def ClassA (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ Integrable f ∧ Integrable (ft f) ∧ (∀ x, f (-x) = f x) ∧ f 0 ≤ 0 ∧
    (ft f 0).re ≤ 0 ∧ f ≠ 0

/-- `A₊(1)² = inf_{f ∈ 𝒜} A(f) A(f̂)`. -/
noncomputable def Aplus2 : ℝ≥0∞ := ⨅ (f : ℝ → ℝ) (_ : ClassA f), A (fun x => (f x : ℂ)) * A (ft f)

/-- `A₊(1) = (A₊(1)²)^{1/2}`. -/
noncomputable def Aplus : ℝ≥0∞ := Aplus2 ^ (1/2 : ℝ)

/-- The class of Problem 6.11 (GGSTW): even, integrable, continuous at `0`, `f(0) < 0`, `f̂(0) < 0`. -/
def Class611 (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ ContinuousAt f 0 ∧ (∀ x, f (-x) = f x) ∧ f 0 < 0 ∧ (ft f 0).re < 0

/-- `C_{6.11}`: the largest `C` with `A(f) A(f̂) ≥ C` on the class of Problem 6.11. -/
noncomputable def C611 : ℝ≥0∞ := ⨅ (f : ℝ → ℝ) (_ : Class611 f), A (fun x => (f x : ℂ)) * A (ft f)

/-- Theorem 1.1 of the paper: `0.5502 < A₊(1) ≤ 0.5509`, i.e. `0.5502² < A₊(1)² ≤ 0.5509²`, and the same
bounds for `C_{6.11}`. -/
def MainStatement : Prop :=
  ENNReal.ofReal ((2751/5000 : ℝ) ^ 2) < Aplus2 ∧ Aplus2 ≤ ENNReal.ofReal ((5509/10000 : ℝ) ^ 2) ∧
  ENNReal.ofReal ((2751/5000 : ℝ) ^ 2) < C611 ∧ C611 ≤ ENNReal.ofReal ((5509/10000 : ℝ) ^ 2)

/-- The upper half of the theorem (Section 5 of the paper: an explicit self-dual Gaussian combination). -/
def UpperStatement : Prop :=
  Aplus2 ≤ ENNReal.ofReal ((5509/10000 : ℝ) ^ 2) ∧ C611 ≤ ENNReal.ofReal ((5509/10000 : ℝ) ^ 2)

/-- The non-strict lower half (Remark 2.3 of the paper: no extremizer needed). -/
def LowerStatementWeak : Prop :=
  ENNReal.ofReal ((2751/5000 : ℝ) ^ 2) ≤ Aplus2 ∧ ENNReal.ofReal ((2751/5000 : ℝ) ^ 2) ≤ C611

/-- Property `(S_r)` (Definition 2.1): every even real integrable self-dual `g` (continuous version)
with `g(0) ≤ 0` and `g ≥ 0` on `|x| > r` vanishes. -/
def Sr (r : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → Integrable g → (∀ x, g (-x) = g x) → ft g = (fun x => (g x : ℂ)) →
    g 0 ≤ 0 → (∀ x, r < |x| → 0 ≤ g x) → g = 0

/-- Theorem 3 of Gonçalves, Oliveira e Silva and Steinerberger (2017): an extremizer exists.  Used only for
the STRICT lower bound, as an explicit hypothesis (not formalized). -/
def ExtremizerHyp : Prop :=
  ∃ g : ℝ → ℝ, Continuous g ∧ Integrable g ∧ (∀ x, g (-x) = g x) ∧ ft g = (fun x => (g x : ℂ)) ∧
    g 0 = 0 ∧ g ≠ 0 ∧ A (fun x => (g x : ℂ)) * A (fun x => (g x : ℂ)) = Aplus2

end SignUnc
