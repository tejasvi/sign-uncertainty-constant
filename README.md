# Bounds for the sign uncertainty constant in dimension one

Certificates, checking programs and Lean proofs for the paper
*Bounds for the sign uncertainty constant in dimension one* by Tejasvi Singh Tomar
(Zenodo, [doi:10.5281/zenodo.23716092](https://doi.org/10.5281/zenodo.23716092)).

## Theorem

Normalize `f̂(ξ) = ∫ f(x) e^{−2πixξ} dx` and let `A(f) = inf{r > 0 : f(x) ≥ 0 for all |x| ≥ r}`.
Let `𝒜` be the set of nonzero even functions `f : ℝ → ℝ` with `f, f̂ ∈ L¹(ℝ)`, `f(0) ≤ 0` and `f̂(0) ≤ 0`, and
let `A₊(1) = inf_{f ∈ 𝒜} √(A(f) A(f̂))`. Then

    2751/5000 < A₊(1) ≤ 5509/10000,   so   0.30272004 < C_6.11 = A₊(1)² ≤ 30349081/100000000 = 0.30349081,

where `C_6.11` is the constant of Problem 6.11 of Georgiev, Gómez-Serrano, Tao and Wagner (arXiv:2511.02864),
defined with `f(0) < 0` and `f̂(0) < 0`. `C_6.11 = A₊(1)²` is Lemma 2.4 of the paper. For `≤`, the lemma uses a result
of Gonçalves, Oliveira e Silva and Ramos (J. Geom. Anal. 31 (2021), Proposition 3 of arXiv:2003.10765). Both bounds
also have Lean 4 proofs (`lean/`, see "Lean proofs"). There the strict lower bounds take the existence of an extremizer
(Theorem 3 of Gonçalves, Oliveira e Silva and Steinerberger) as a hypothesis, and the lower bounds for `C_6.11` are
proved for real-valued `f`.

## Proof outline

Lower bound:

1. **Reduction** (Lemma 2.2). An extremizer exists (Gonçalves, Oliveira e Silva and Steinerberger, Theorem 3), so it
   suffices to show that every even self-dual `g ∈ L¹` with `g(0) ≤ 0` and `g ≥ 0` on `|x| > r` vanishes.
2. **Criterion** (Theorem 3.4). A certificate consists of Gaussian pairs `(a, s, c)`, cosine terms `(β, d)` with
   `β ≥ r`, `d ≥ 0`, and an even polynomial `ψ`. With
   `b(x) = e^{−πa(x−s)²} + e^{−πa(x+s)²}`, `b̂(y) = 2a^{−1/2} e^{−πy²/a} cos(2πsy)`,

       v   = Σ c (b − b̂) + Σ d cos(2πβ·),       φ = (1 − v + ψ) on [−r, r],  0 outside,
       W   = 1 − v + φ̂,                          ρ = φ̂ − ψ on [−r, r],
       κ(r) = (2r² + Si(4πr²)/(2π))^{1/2},

   the conditions `κ(r) < 1`, `W ≥ m` on `(r, ∞)`, `|ρ| ≤ e` on `[0, r]` and `m > 2re/(1 − κ(r))` imply
   `A₊(1) > r`. The proof uses the identity `g(0) = ∫_{|y|>r} gW + Σ d g(β) + ∫_{−r}^{r} gρ` for self-dual `g`
   and the bound `‖(Id − K)⁻¹‖ ≤ 1/(1 − κ(r))` for the integral operator `K` with kernel `cos(2πxy)` on `[−r, r]`.
3. **Verification.** Programs 1 and 2 check the four conditions for `certs/cert_r05502_K35.json` in ball arithmetic.

Upper bound (Lemma 5.1): if `g = Σ c (b + b̂)` satisfies `g(0) < 0` and `g ≥ 0` on `[r, ∞)`, then `g` is an even
self-dual function in both classes and `A(g) A(ĝ) ≤ r²`. Programs 3 and 4 check the two inequalities for
`certs/pcert_r05509_NR2.json` (`r = 5509/10000`).

## Files

| Path | Content |
|---|---|
| `certs/cert_r05502_K35.json` | lower bound, `r = 2751/5000`: 530 Gaussian pairs, 5 cosine terms, `ψ` of degree 40 |
| `certs/cert_r05485_X30.json` | lower bound without cosine terms, `r = 1097/2000` (450 Gaussian pairs) |
| `certs/cert_r0548_X30.json` | lower bound without cosine terms, `r = 137/250` (450 Gaussian pairs) |
| `certs/pcert_r05509_NR2.json` | upper bound, `r = 5509/10000`: 1808 Gaussian pairs (1605 on a grid, 202 narrow pairs with centers in [2/5, 3], and one wide pair) |
| `certs/controls/` | perturbed copies of the two main certificates (see Controls) |
| `checker/check_cert_pm.py` | program 1 (Gauss–Legendre quadrature with a Bernstein-ellipse error bound, 192-bit balls) |
| `checker/check_cert.py` | program 1 for certificates without cosine terms (the same code without them) |
| `checker/indep_check_pm.py` | program 2 (closed forms with the complex error function, 256-bit balls) |
| `checker/indep_check.py` | earlier version of program 2 for certificates without cosine terms |
| `checker/check_primal.py` | program 3 (upper bound: Taylor bounds on `[r, Y]`, dominant-Gaussian tail, 192-bit balls) |
| `checker/indep_primal.py` | program 4 (upper bound: interpolation bounds on `[r, 2Y]`, vertex tail bound, Arb and mpmath) |
| `logs/` | logs of the runs in Tables 1 and 2 of the paper and of the controls |
| `search/` | the linear programs and certificate generators (not needed for checking) |
| `tests/` | floating-point checks used in the remarks of the paper (not part of the proof) |
| `lean/` | the Lean 4 proofs of the bounds (see "Lean proofs") |
| `paper/` | the LaTeX source of the paper (version 6), the data of its Figure 1 (`fig_g.dat`, `fig_W.dat`) and `fig_data.py`, which computes them from the certificates in floating point (not part of the proof) |

SHA-256 checksums of all files are in `SHA256SUMS`.

Programs 1 and 2 were written separately, as were programs 3 and 4. Within each pair the two programs share only the
certificate format, the statement they check (for programs 1 and 2, Theorem 3.4 of the paper, which their docstrings
call "Lemma certificate") and one-line helpers.

## Certificate formats

All numbers are strings of exact fractions. The programs convert them to exact fractions and then to balls, so no
certificate number passes through floating point.

Lower bound:

- `"r"`: the radius, for example `"2751/5000"`;
- `"gauss"`: entries `[a, s, c, 0]` (Gaussian pair with width `a > 0`, center `s ≥ 0`, coefficient `c`; the fourth
  entry must be `0`);
- `"pm"`: entries `[β, d]` (cosine term `d cos(2πβx)`, with `β ≥ r` and `d ≥ 0`); absent if there are none;
- `"psi"`: `[q_0, …, q_20]` with `ψ(x) = Σ_k q_k x^{2k}`.

Upper bound: `"r"` and `"gauss"` with entries `[a, s, c]`, defining `g = Σ c (b + b̂)`. The pair with the smallest
`a` must be unique, with `c > 0` and the largest center. Programs 3 and 4 use it for the tail.

## Checking

The programs need Python 3 (we used 3.12.13) and `python-flint` (we used 0.9.0). Program 4 also needs `mpmath`
(we used 1.4.1):

    pip install python-flint==0.9.0 mpmath

Lower bound (`r = 2751/5000`):

    python3 checker/check_cert_pm.py certs/cert_r05502_K35.json --m 1/10000 --e 1/10000000 \
        --N 1600 --rho 11/10 --YT 1500 --w0 1/500 --workers 32
    python3 checker/indep_check_pm.py certs/cert_r05502_K35.json --m 3/50000 --e 1/500000 --hrho 1/150000 \
        --YT 1500 --nibp 8 --h0far 1/50 --workers 10

The result lines must read `RESULT: PASS => A_+(1) > 2751/5000 and C_6.11 > 7568001/25000000 = 0.30272004` and
`[indep] RESULT: PASS (A_+(1) > 2751/5000)`, and both programs exit with status 0. The logged runs took 735 s and 1697 s
of wall-clock time on a shared server.

Upper bound (`r = 5509/10000`):

    python3 checker/check_primal.py certs/pcert_r05509_NR2.json --workers 24
    python3 checker/indep_primal.py certs/pcert_r05509_NR2.json --workers 20

The result lines must read `RESULT: PASS => A_+(1) <= 5509/10000 and C_6.11 <= 30349081/100000000 = 0.30349081` and
`[indep-primal] RESULT: PASS  (A_+(1) <= 5509/10000, C_6.11 <= 30349081/100000000 = 0.30349081)`. The logged runs
took 109 s and 302 s.

Certificates without cosine terms:

    python3 checker/check_cert.py certs/cert_r05485_X30.json --m 1/500 --e 1/10000000 --N 500 --YT 300 \
        --w0 1/500 --workers 40
    python3 checker/indep_check.py certs/cert_r05485_X30.json --m 1/1000 --e 1/40000 --YT 300 --nibp 8 --workers 30
    python3 checker/check_cert.py certs/cert_r0548_X30.json --m 1/400 --e 1/10000000 --N 500 --YT 300 \
        --w0 1/500 --workers 40
    python3 checker/indep_check.py certs/cert_r0548_X30.json --m 1/500 --e 1/20000 --YT 300 --nibp 8 --workers 30

`check_cert_pm.py` also accepts certificates without cosine terms, since the `"pm"` list is optional.

Several input checks are `assert` statements: for example β ≥ r and d ≥ 0, the tail conditions of programs 3 and 4,
and κ(r) < 1 in program 2. Since `python -O` would remove them, each program stops at start-up under `-O` with
the message `this checker relies on assert statements; run it without -O`.

### What the logs contain

| Log (`logs/`) | Certificate | Program | Key lines |
|---|---|---|---|
| `program1_cert_r05502_K35.log` | `cert_r05502_K35.json` | 1 | κ < 0.943802; W ≥ 0.0001 on [r, 1500] (805,759 interval evaluations); W ≥ 0.0427 on [1500, ∞); sup\|ρ\| ≤ 1.486e−10 |
| `program1_cert_r05502_K35_rerun.log` | `cert_r05502_K35.json` | 1 | independent rerun (see Provenance) |
| `program2_cert_r05502_K35.log` | `cert_r05502_K35.json` | 2 | W ≥ 0.00006 on [r, 1500] (192,401 intervals); W ≥ 0.0427 on [1500, ∞); \|ρ\| ≤ 2e−6 |
| `program1_cert_r05485_X30.log` | `cert_r05485_X30.json` | 1 | W ≥ 0.002 on [r, 300] (187,420 interval evaluations); W ≥ 0.6733 on [300, ∞) |
| `program2_cert_r05485_X30.log` | `cert_r05485_X30.json` | 2 | W ≥ 0.001 on [r, 300] (209,781 intervals); W ≥ 0.6762 on [300, ∞) |
| `program1_cert_r0548_X30.log` | `cert_r0548_X30.json` | 1 | W ≥ 0.0025 on [r, 300] (168,332 interval evaluations); W ≥ 0.6742 on [300, ∞) |
| `program2_cert_r0548_X30.log` | `cert_r0548_X30.json` | 2 | W ≥ 0.002 on [r, 300] (180,951 intervals); W ≥ 0.6770 on [300, ∞) |
| `program3_pcert_r05509_NR2.log` | `pcert_r05509_NR2.json` | 3 | g(0) < −1.000006e−8; g > 0 on [r, 92] (36,254 intervals, smallest bound 9.96e−9); g/G ≥ 1.93021e−5 on [92, ∞) |
| `program3_pcert_r05509_NR2_rerun.log` | `pcert_r05509_NR2.json` | 3 | independent rerun (see Provenance) |
| `program4_pcert_r05509_NR2.log` | `pcert_r05509_NR2.json` | 4 | g(0) in Arb and mpmath; g > 0 on [r, 184] (107,499 intervals); g/G ≥ 1.93021e−5 on [92, ∞) |

See Provenance for how these logs relate to the programs in `checker/`.

### Controls

Each control must fail under the programs that check it (`RESULT: FAIL`, or `rejected` when an input condition fails).
Logs are in `logs/controls/`. A negative lower bound on a small interval shows that the check fails there, but does not
by itself prove that the function is negative.

| Control | Programs 1/3 | Programs 2/4 |
|---|---|---|
| primary lower-bound data with `--m 17/100000`, above the value `W(2.9194477) < 0.0001633` | program 1 fails near y = 2.9195 (`program1_m000017.log`) | not run |
| `controls/neg_K35b_r05507.json`: lower-bound data with `r = 5507/10000` (cosine at β = r moved with it) | program 1 fails the checks of W (lower bound −0.038 near y = 32.49) and ρ (`program1_neg_K35b_r05507.log`) | program 2 fails the checks of W (lower bound −0.028 in [26.80, 27.05]) and ρ (`program2_neg_K35b_r05507.log`) |
| `controls/neg_K35b_perturb.json`: one coefficient `c` increased by 0.1 | program 1 fails the checks of W (lower bound −0.059 near y = 20.17) and ρ (`program1_neg_K35b_perturb.log`) | program 2 fails the checks of W (lower bound −0.02 in [19.80, 20.05]) and ρ (`program2_neg_K35b_perturb.log`) |
| `controls/neg_K35b_beta_inside.json`: the cosine at β = 2751/5000 moved to β = 5499/10000 < r | rejected on input | rejected on input |
| `controls/upper_r05505.json`: upper-bound data with `r = 1101/2000`, below the last zero of g (≈ 0.5508999) | program 3 fails at y ≈ 0.5508999 | program 4 fails at y ≈ 0.5508999 |
| `controls/upper_g0pos.json`: the coefficient of `(a, s) = (1, 0)` raised so that g(0) = +1.0e−8 | fails (g(0) ≥ 0) | fails |
| `controls/upper_dip70.json`: the coefficient of `(16, 70)` lowered by 0.001 | fails (failing intervals in [0.5859, 1.0309], [2.3109, 3.0759], [3.9109, 4.0309] and [69.7159, 70.2759]) | fails (negative lower bounds near y = 0.80, 1.03, 2.55, 2.80, 3.05, 3.07, 4.03 and in [69.55, 70.30]) |
| `controls/upper_wide_hat.json`: an extra pair `(4096, 1/4, 1e−12)`, which makes g negative far out | rejected (tail conditions) | rejected (tail conditions) |
| `controls/upper_tail_neg.json`: the coefficient of the wide pair made negative | rejected | rejected |

## Floating-point checks (`tests/`)

These support statements in the remarks of the paper and are not part of the proof.

- `wmin_eval.py`: value of `W` in ball arithmetic (program 2's closed form) at numerically located minimizers:
  `W(2.9194477) = 0.000163201886287 ± 3.0e−17` for the primary certificate, so `0.0001 ≤ inf W < 0.0001633`.
- `identity_test.py`: the identity `g(0) = ∫_{|y|>r} gW + Σ d g(β) + ∫_{−r}^{r} gρ` for eight self-dual test
  functions (Hermite functions `h_0, h_4, h_8, h_12` and four sums `b + b̂`), relative error below `1e−12`.
- `wshape.py`: a scan of `W` on `[r, 40]` (the intervals where `W < 0.0015`).
- `v0_baseline2.py`: the certificate with no Gaussian pairs and no cosine terms, for which `W = 1 + φ̂` stays positive for
  `r < 0.45355`.
- `cert_properties.py`: every property of the certificates stated in the paper (numbers of pairs, widths and centers,
  sizes and denominators of the coefficients, cosine terms, `ψ`, the wide pair of the upper bound), computed from the
  JSON files in exact arithmetic with the standard library (`logs/tests/cert_properties.log`).

Usage: `python3 -B tests/<script>.py <certificate>`. For `wmin_eval.py` the argument is the `checker/` directory.
`wshape.py` also takes `Ymax step threshold` and optionally a point at which to print `W`, for example
`40 0.0005 0.0015 2.9194477`, and `v0_baseline2.py` takes no argument.

## How the certificates were found (`search/`)

The checks do not depend on how the certificates were found. The scripts need `numpy`, `scipy`, `mpmath` and `highspy`.

Lower bound. For fixed `r`, Gaussian pairs and cosine frequencies, `φ` is replaced by the Nyström solution of
`(Id − K)φ = 1 − v`, so that `W` is affine in the coefficients. The linear program maximizes `t` subject to `W ≥ t`
on a grid of `[r, 1500]`, `|c| ≤ 1000`, `d ≥ 0` and `Σ d ≤ 0.95`, and adds the local minima of `W` on a finer grid as
cutting planes. `lp_g2.py` holds the closed forms (Faddeeva function). `hsolve.py` and `hsolve2.py` call the HiGHS
interior point method, and `hsolve2.py` retries failed solves with other settings. `gen_cert.py` and `gen_cert3.py`
round the solution to rationals and compute `ψ` from the moments of `φ`.

Primary certificate. We used `lp_cgd10.py`, a version of `lp_cgd6.py` that scales the columns for the interior point
method and uses a finer coarse grid:

    cd search
    python3 lp_cgd10.py --r 0.5502 --X 35 --cmax 1000 --ds 0.2 --widths 2,8,32 --pm 0.56:2.5:0.01 \
        --pmnear 0,0.0001,0.0005,0.001,0.002,0.003,0.005,0.0075 --dsum 0.95 --iters 30 --out k_X35_0.5502.json
    python3 gen_cert3.py k_X35_0.5502.json cert_r05502_K35.json 2751/5000

The runs in `lp_outputs/log_S30_5502.txt` and `lp_outputs/log_T45_5503.txt`, which returned negative values of `t` for
`r = 0.5502` and `r = 0.5503` (Section 7 of the paper), come from an earlier version of these scripts.

Certificates without cosine terms:

    python3 lp_cg.py --r 0.5485 --X 30 --ds 0.2 --out cg_r0.5485_X30.json
    python3 gen_cert.py cg_r0.5485_X30.json cert_r05485_X30.json 1097/2000

Applied to the recorded `lp_outputs/k_X35_0.5502.json`, `gen_cert3.py` reproduces the Gaussian pairs and cosine terms
of `certs/cert_r05502_K35.json` exactly. Depending on the floating-point library, the coefficients of `ψ` can differ in
the 16th significant digit. This changes only the residual `ρ`, which the checks bound.

Upper bound (`search/upper/`). `primal5.py` maximizes `ε` subject to `g ≥ ε w` on a grid of `[r, Y]`, `g(0) ≤ 0` and
`|c| ≤ cmax`, where `w = 1` up to the largest center `X` and `w` decays like the wide pair beyond it. Cutting planes
are added as above. `gen_primal.py` rounds the coefficients to multiples of `1e−12` and lowers the coefficient of the
pair `(1, 0)` so that `g(0)` is about `−1e−8`. `primal_lp.py` holds the basis functions. `primal7.py` is a version of
`primal5.py` with sparse matrices that also accepts narrow pairs (`--extra a:s0:s1:ds`). We used

    cd search/upper
    python3 primal7.py --X 80 --ds 0.25 --widths 1,2,4,8,16 --A 2048 --extra 64:0.4:3:0.02 \
        --extra 256:0.5:1.2:0.01 --rs 0.5509 --out pr7_NR2_0.5509.json
    python3 gen_primal.py pr7_NR2_0.5509_r0.5509.json pcert_r05509_NR2.json 5509/10000

Applied to the recorded `lp_outputs/pr7_NR2_0.5509_r0.5509.json`, `gen_primal.py` reproduces
`certs/pcert_r05509_NR2.json` exactly. `tests/cert_properties.py` computes the properties of `pcert_r05509_NR2.json`
stated in the paper, including `max |c| = 0.999999977971` and the adjusted `(1, 0)` coefficient, which is the only one
that is not a multiple of `1e−12`.

## Lean proofs (`lean/`)

`lean/` contains proofs in Lean 4, with Mathlib, of the statements

    def UpperStatement : Prop :=
      Aplus2 ≤ ENNReal.ofReal ((5509 / 10000) ^ 2) ∧ C611 ≤ ENNReal.ofReal ((5509 / 10000) ^ 2)
    def LowerStatementWeak : Prop :=
      ENNReal.ofReal ((2751 / 5000) ^ 2) ≤ Aplus2 ∧ ENNReal.ofReal ((2751 / 5000) ^ 2) ≤ C611
    def MainStatement : Prop :=
      ENNReal.ofReal ((2751 / 5000) ^ 2) < Aplus2 ∧ Aplus2 ≤ ENNReal.ofReal ((5509 / 10000) ^ 2) ∧
      ENNReal.ofReal ((2751 / 5000) ^ 2) < C611 ∧ C611 ≤ ENNReal.ofReal ((5509 / 10000) ^ 2)

in the following theorems (namespace `SignUnc`):

| theorem | statement | file |
|---|---|---|
| `upperK` | `UpperStatement` | `SignUnc/UpperMainK.lean` |
| `lower_weakK` | `LowerStatementWeak` | `SignUnc/LowerMainK.lean` |
| `lower_strictK` | `ExtremizerHyp → ENNReal.ofReal ((2751 / 5000) ^ 2) < Aplus2 ∧ ENNReal.ofReal ((2751 / 5000) ^ 2) < C611` | `SignUnc/LowerMainK.lean` |
| `mainK` | `ExtremizerHyp → MainStatement` | `SignUnc/MainK.lean` |
| `aplus2_pos_finiteK` | `0 < Aplus2 ∧ Aplus2 < ⊤` | `SignUnc/ProbeK.lean` |

The definitions are in `SignUnc/Defs.lean`. Here `ft f` is Mathlib's Fourier transform of `f` (the normalization above)
and `A f ∈ [0, ∞]` is the infimum of the `r > 0` such that `f(x)` is real and nonnegative for `|x| ≥ r`. `Aplus2` is the
infimum of `A(f) A(f̂)` over the class `𝒜` above, with `f` continuous (the continuous versions), and `C611` is the
infimum over the even integrable real `f` that are continuous at `0` with `f(0) < 0` and `Re f̂(0) < 0`, that is, the
class of Problem 6.11 for real-valued `f`. The statements compare squares, which is equivalent to the form
`2751/5000 < A₊(1) ≤ 5509/10000` of the paper. The class for real-valued `f` is part of the class for complex-valued
`f`, so the bound of `upperK` for `C611` also bounds the infimum over complex-valued `f`. The lower bounds for `C611`
are proved only for real-valued `f`: the step of Lemma 2.4 of the paper that shows that a function of the class of
Problem 6.11 is real when `A(f)` and `A(f̂)` are finite is not formalized. `SignUnc/APos.lean` proves `A(f) > 0` and
`A(f̂) > 0` on both classes (`A_pos_classA`, `A_ft_pos_classA`, `A_pos_class611`, `A_ft_pos_class611`), so that no
product `A(f) A(f̂)` in the infima is `0 · ∞`.

`lower_weakK` has no hypotheses. The strict lower bounds, in `lower_strictK` and `mainK`, assume

    def ExtremizerHyp : Prop :=
      ∃ g : ℝ → ℝ, Continuous g ∧ Integrable g ∧ (∀ x, g (-x) = g x) ∧ ft g = (fun x => (g x : ℂ)) ∧
        g 0 = 0 ∧ g ≠ 0 ∧ A (fun x => (g x : ℂ)) * A (fun x => (g x : ℂ)) = Aplus2

the statement of Theorem 3 of Gonçalves, Oliveira e Silva and Steinerberger (an extremizer exists), which the paper uses
in Lemma 2.2 and which is not formalized here. It is a hypothesis of these two theorems, not an axiom.
`SignUnc/Lower/ExtremizerProbe.lean` checks that the hypothesis cannot fail for a formal reason, such as a junk value,
which would make the two theorems vacuous. Its first six conditions hold for an explicit combination of Gaussians
(`probe_clauses`). Every `g` that satisfies them lies in `𝒜`, so that `A₊(1)² ≤ A(g)²`, and has `A(g) > 0` (`probe_le`),
so the last condition says that `g` attains the infimum `A₊(1)²`. `aplus2_pos_finiteK` gives `0 < A₊(1)² < ∞` from
`lower_weakK` and `upperK`. Whether such a `g` exists is the content of the cited Theorem 3, which the probe does not
prove.

### The upper bound

The proof follows Section 5 of the paper:

- `SignUnc/Gauss.lean`: the Fourier transforms of `b` and `b̂`, from Mathlib's `fourier_gaussian_pi'` and Fourier
  inversion;
- `SignUnc/Upper.lean`: Lemma 5.1;
- `SUCert/IvalCore.lean` and `SignUnc/Ival/`: ball arithmetic with dyadic centres and radii, and its soundness;
- `SUCert/Jet.lean`, `SUCert/JetK.lean` (with definitions from `SUCert/Chk.lean`, `Chk3.lean` and `Grid.lean`): the
  checker. `[r, 92]` is covered by consecutive segments, each with a Taylor order `n`, a list of terms of `g` that are
  left out on it, and a subdivision into pieces. The checker bounds the omitted terms on the whole segment. On a piece
  `[y₀ − η, y₀ + η]` it computes the Taylor polynomial of order `n` at `y₀` of the sum of the remaining terms, from
  their moments grouped by width, bounds the Taylor coefficient of order `n + 1` on the piece, and verifies in exact
  integer arithmetic, by bisection and Taylor shifts, that the polynomial minus these bounds is positive on the piece.
  The base check tests `g(0) < 0` and the tail bound of Section 5 on `[92, ∞)`, and that the segments are contiguous
  and cover `[r, 92]`;
- `SignUnc/Jets.lean`, `JetSound.lean`, …, `JetSound4.lean`, `OmitSound.lean`, `PolySound.lean`, `TaylorN.lean`,
  `TaylorK.lean`, `PieceSound.lean` and `UpperK.lean`, with `Calc.lean`, `Calc3.lean`, `Tail.lean`, `ChkSound.lean`
  and `GridSound.lean`: the soundness of the checker (`SignUnc.Chk.upper_v4_sound`);
- `SUCert/DataGroups.lean`: the 1808 pairs of `certs/pcert_r05509_NR2.json`, grouped by width; `SUCert/UpperCfgK.lean`
  and `SignUnc/UpperShardsK/S0.lean`, …, `S729.lean`: 730 consecutive segments that cover `[r, 92]`, with Taylor orders
  from 6 to 16 and 2,569 pieces in all, each segment checked by one `decide +kernel`; `SignUnc/UpperShardsK/Base.lean`:
  the base check; `SignUnc/UpperMainK.lean`: the theorem.

### The lower bound

The proof follows Sections 2 to 4 of the paper, with the certificate `certs/cert_r05502_K35.json`:

- `SignUnc/Lower/Identity.lean`: certificates and the identity of Lemma 3.2;
- `SignUnc/Lower/Apriori.lean`: Lemma 3.3;
- `SignUnc/Lower/Criterion.lean`: Theorem 3.4. Its last step uses Lemma 3.3 instead of analytic continuation;
- `SignUnc/Lower/Kappa.lean`: `κ(2751/5000) ≤ 0.9503`, from `cos²θ ≤ 1 − (θ − θ³/6)²` for `θ² ≤ 6`;
- `SignUnc/Lower/Dilation.lean`: Remark 2.3, that is `A₊(1)² ≥ r²` from `(S_r)` without extremizers. That `f + f̂`
  is nonzero follows from `κ(r) < 1` instead of analytic continuation;
- `SignUnc/Lower/Strict.lean`: Lemma 2.2 with `ExtremizerHyp`;
- `SignUnc/Lower/Fejer.lean`: the first part of Lemma 2.4 (`Aplus2 ≤ C611`), with a Gaussian in place of the Fejér
  kernel;
- `SUCert/Low.lean`: the checker, in ball arithmetic with precision `2^-128`. It replaces `φ` on `[0, r]` by a
  piecewise polynomial `p` and checks: `|φ − p| ≤ ε` on each piece, from the Taylor polynomial of `φ` of order 32 at the
  centre of the piece and a bound for the next coefficient on the piece (then `|φ̂ − p̂| ≤ 2rε` everywhere);
  `|p̂ − ψ| + 2rε ≤ δ` on `[0, r]`, from the power series of `p̂ − ψ`, whose coefficients up to degree 58 are computed
  from the moments of `p`, and a bound for the rest; `1 − v + p̂ > m + 2rε` on `(r, 300]`, on consecutive segments with
  Taylor polynomials in `y` built from the moments of the pieces of `p` and the positivity test of the upper bound; and
  the same inequality on `[300, ∞)`, by repeated integration by parts in the integral that defines `p̂`, piece by
  piece;
- `SUCert/LowData.lean`: the certificate; `SUCert/LowP.lean`: `p`, with 19 pieces of degree 24; `SUCert/LowCfg.lean`:
  `m = 10⁻⁴`, `ε = 5·10⁻⁷`, `δ = 10⁻⁶`, each rounded up to a multiple of `2^-128`; `SUCert/LowSegs.lean`: 118
  segments that cover `(r, 300]`, with Taylor orders 16 and 20 and 967 pieces in all;
- `SignUnc/LowTaylor.lean`, `SignUnc/LowSound1.lean`, …, `LowSound7.lean` and `SignUnc/LowFinal.lean`: the soundness of
  the checker and the assembly (`lower_weak_of`, `lower_strict_of`, `main_of`). Conditions (i) and (iv) of Theorem 3.4
  follow from `κ ≤ 0.9503` and `2rδ < m(1 − 0.9503)`;
- `SignUnc/LowK/`: the tables of moments of the pieces of `p` used by the segment checks, written out as literals
  (`MomsLit16.lean`, `MomsLit20.lean`), the segment check with the table as an argument (`Defs.lean`) and the glue lemmas
  (`Glue.lean`);
- `SignUnc/LowShardsK/`: the 142 checks, each one `decide +kernel`: `B_p0`, …, `B_p18` (the pieces of `p`), `B_rho`
  (the bound for `ρ`), `B_tail` (`[300, ∞)`), `B_misc` (the pieces of `p` cover `[0, r]` and the segments cover
  `(r, 300]`), `B_m16` and `B_m20` (the literal tables equal the computed moments) and `S0`, …, `S117` (one per
  segment); `SignUnc/LowShardsK.lean` collects them, and `SignUnc/LowerMainK.lean` states the theorems.

### Axioms

`decide +kernel` has the Lean kernel itself evaluate each of the 873 checks (731 for the upper bound, 142 for the lower
bound), and does not run the compiled code, so the Lean compiler is not part of the trusted base, although
`lakefile.toml` builds `SUCert` with `precompileModules = true`. `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound` for `upperK`, `lower_weakK`, `lower_strictK`, `mainK`, `aplus2_pos_finiteK`,
`probe_clauses`, `probe_le` and the four lemmas of `SignUnc/APos.lean` (`results/axioms_shipped.txt`). In a separate
check, the proofs were built again on two other machines, every module outside Mathlib was checked again by Lean's
kernel, and the exported proofs, one for each check and one for the rest of the proof with the checks as axioms, were
accepted by `leanchecker` and by two further implementations of the Lean kernel, nanoda and lean4lean.

### Building

The build needs Linux and at least 64 GB of memory: the largest check needs 44 GB, and `tools/kbuild.py` (below) kills
and restarts a check whenever less than 12 GB of memory remain available (here GB means 10⁹ bytes; the logs give KiB).
With the toolchain `leanprover/lean4:v4.35.0-rc3` from `lean/lean-toolchain` and Mathlib `v4.35.0-rc3`:

    cd lean
    lake exe cache get          # prebuilt Mathlib
    lake build SignUnc.LowK.Glue SUCert.UpperCfgK SUCert.DataGroups SignUnc.LowFinal SignUnc.UpperK SignUnc.APos \
      SignUnc.Lower.ExtremizerProbe
    python3 tools/kbuild.py tools/kjobs.txt MEMCAP_GB MAXJOBS
    bash tools/kfinal.sh

The `lake build` command builds the modules that the check modules and the final modules import. It prints warnings from
Lean's linters (deprecated names, unused `simp` arguments, unused variables), but no errors.

`tools/kbuild.py` compiles the 873 check modules, one Lean process for each
(`lake env lean --tstack=1000000 -DElab.async=false -o ...`, longest first; the large thread stack is needed for the
deep kernel reductions of the checks). At most `MAXJOBS` processes run at once, and their memory estimates (the third
column of `tools/kjobs.txt`, in GB) add up to at most `MEMCAP_GB`. If the available memory falls below 12 GB, the script
kills the most recently started process and queues it again with twice its memory estimate. A second run skips the
checks that are recorded as done in `logs/kbuild.tsv`.

`tools/kfinal.sh` checks the outputs of the 873 modules, compiles `SignUnc/LowShardsK.lean`, `UpperMainK.lean`,
`LowerMainK.lean`, `MainK.lean` and `ProbeK.lean`, and runs `lake env lean Axioms.lean`, which prints the statements and
their axioms. `results/axioms_shipped.txt` is this output for this tree. The build has succeeded if `tools/kfinal.sh`
reports `bad=0` and `rc=0` for the final modules and `lake env lean Axioms.lean | diff - results/axioms_shipped.txt`
prints nothing.

After changing a source file, delete `logs/kbuild.tsv` and `.lake/build` before building again: `tools/kbuild.py` skips
the checks recorded as done, and `tools/kfinal.sh` does not compare the compiled files with the sources. We have not
tried a plain `lake build`, which builds the same modules but starts one job per core whatever their memory needs.

On a machine with 128 virtual CPUs and 2 TB of memory (`MEMCAP_GB` 1611, `MAXJOBS` 128), the first `lake build` took 3.5
minutes, the 873 checks 11.1 minutes (17.8 CPU-hours) and `tools/kfinal.sh` 25 seconds, about 18 CPU-hours in all. An
earlier build of the same checks on a machine with 192 virtual CPUs took 13.1 CPU-hours. A check of the lower bound
needs up to 44 GB of memory (16 GB for the median one), a check of the upper bound up to 11 GB (5 GB for the median
one), and the other modules up to 7 GB. On a smaller machine, set `MEMCAP_GB` somewhat below its memory, for example 110
on a machine with 128 GB; the build then takes about two hours or more, depending on the processor.

If `lake exe cache get` stops with "No file descriptors available (os error 24)", raise the limit on open files (for
example `ulimit -n 65536`).

### Regenerating the data

In `lean/`, the commands

    python3 tools/gen_upper_groups.py ../certs/pcert_r05509_NR2.json SUCert/DataGroups.lean
    python3 toolsk/gen_shards_k.py data/v4_gen/sweep . 120 345
    python3 tools/gen_lower_data.py ../certs/cert_r05502_K35.json SUCert/LowData.lean
    python3 tools/gen_lowsegs.py data/low_gen SUCert/LowSegs.lean
    python3 tools/gen_lowshards_k.py

regenerate byte for byte `SUCert/DataGroups.lean`; `SUCert/UpperCfgK.lean`, the upper check modules,
`SignUnc/UpperMainK.lean` and `data/k_shards.check`; `SUCert/LowData.lean`; `SUCert/LowSegs.lean`; and the 142 lower
check modules, `SignUnc/LowShardsK.lean` and `tools/lowshards_k.jobs`. Two generators are Lean programs, which need the
first `lake build` above. `lake env lean tools/GenMoms.lean` writes `tmp/MomsLit16.lean` and `tmp/MomsLit20.lean`, which
are identical to `SignUnc/LowK/MomsLit16.lean` and `MomsLit20.lean`. `lake exe genlow mkp 24 8 5 10000000 70 OUT`
(source `SignUnc/GenLow.lean`) writes the list of the pieces of `p` that forms lines 9 to 29 of `SUCert/LowP.lean`.

Of the executables declared in `lakefile.toml`, only the generator `genlow` (source `SignUnc/GenLow.lean`) is included;
the others (benchmarks and the generator `genjet`) are not needed. The input files were written by compiled Lean
programs outside the proof. In `data/v4_gen/sweep/` (from the generator `genjet`, not included), for each of 105
segments of `[r, 92]` and three or four orders `n`, a line gives the segment start, the terms left out in each group,
the piece widths, whether a compiled run of the checker accepted the segment and how long it took;
`toolsk/gen_shards_k.py` takes for each segment the fastest order, copies its pieces and choice of terms into the Lean
files, and splits the 105 segments into 730. Each file in `data/low_gen/` (from `genlow gen`) gives the start, the
Taylor order, the number of series terms, the included terms and the piece widths of one segment of `(r, 300]`, and how
long a compiled run of the checker took on it. The proofs do not depend on these choices: the kernel checks every
segment and every piece of `p`, and the base checks check that the segments are contiguous and cover `[r, 92]` and
`(r, 300]`.

## Provenance

The logs listed under "What the logs contain" were produced by the independently reviewed versions of the six programs.
The exception is `program3_pcert_r05509_NR2.log`, which comes from the program in `checker/`. The files here differ from
the versions we ran in two places:

- `checker/`: every program stops at start-up under `python -O` (see Checking), and one docstring sentence in
  `check_cert.py`, `check_cert_pm.py` and `check_primal.py` now deduces the bound on `C_6.11` directly from the
  definitions instead of from the equality `C_6.11 = A₊(1)²` (Lemma 2.4).
- `search/upper/primal5.py` and `search/upper/gen_primal.py`: a line that added a local directory to `sys.path` has been
  removed.

The Lean files in `lean/` are those of the formalization at the version we built; no check module or generated file
was changed. The exceptions are:

- `Axioms.lean`, `results/axioms_shipped.txt` and the library roots `SignUnc.lean` and `SUCert.lean`, which were
  written for this archive; the library roots import only the modules of these proofs;
- `tools/kbuild.py` and `tools/kfinal.sh`, versions written for this archive of the scripts that ran our builds;
- `tools/kjobs.txt`, which lists the check modules with the run times measured in our earlier builds and memory
  estimates somewhat above the measured peaks;
- three comment lines: two that named modules by their earlier names, and a shortened docstring line in
  `tools/gen_lowshards_k.py`.

The headers of `MomsLit16.lean` and `MomsLit20.lean` name the generator by its original path
`SignUnc/Test11b/GenMoms.lean`; it ships as `tools/GenMoms.lean`. A comment in `lakefile.toml` mentions `native_decide`,
which these proofs do not use.

`logs/release_reruns/` holds the output of the programs in `checker/` on the certificates of Tables 1 and 2 of the paper. These
logs reproduce the corresponding logs above. The two `_rerun` logs in `logs/` come from separate runs of the same
programs on separate copies of the certificates, and they are identical to the logs above apart from the times and
the last digits of the ball that program 1 prints for ∫|φ⁽⁶⁾|, which depend on the order of summation.

## Versions

Version 6 (tag `v6`) goes with version 6 of the paper, which has a new abstract, a revised introduction, a figure and a
shorter Section 6 (the details of the Lean proofs are in this README). In that version the bounds for `C_6.11` form
Corollary 1.2; the docstrings of the Lean files, written for earlier versions, count them as part of Theorem 1.1. Version 6
adds the directory `paper/` with the paper's LaTeX source and the data of its figure. The certificates, programs, logs and
Lean files are those of version 5, which is commit `969f854b59fa` of this repository.

## License

Code: Apache-2.0 (see `LICENSE`). Paper and data: CC BY 4.0.
