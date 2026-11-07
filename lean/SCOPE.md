# Scope of the formalization

Pinned environment: Lean v4.34.0-rc2, Mathlib
85e3a25e006c35636f0e53b0e9296caca2685bc0. Result, equation and page numbers
refer to [paper/main.pdf](../paper/main.pdf) (28 pages). Lean indices are 0-based where the
paper is 1-based; this is stated at each place where it matters.

The aggregate `KE02.CoreCertificate` has no hypotheses. Each component below
is a structure of statements quantified over all of the displayed variables;
the hypotheses listed are the only ones.

## Definitions

* `secant F u v = (F v - F u)/(v - u)`.
* `centeredVariation F h t` is (13):
  `(F(t+h) - F t)/h - (F t - F(t-h))/h`.
* `endpointVariation F θ h t` is (33):
  `(F(t+h) - F(t+(1-2θ)h))/(2θh) - (F(t-(1-2θ)h) - F(t-h))/(2θh)`. The paper
  defines it for `0 < θ ≤ 1/2`; the Lean formula takes any real `θ`, and each
  statement about it carries its own range of `θ`.
* `centeredEstimate` and `endpointEstimate` are the same formulas applied to
  given real numbers (the computed quantities written with a hat).
* `triangleWeight t h x = max (1 - |x - t|/h) 0`.
* `alg2K n` is the least natural number `K` with `16n³ ≤ 2^K`;
  `alg2Theta n = 1/(4K)`; `basicK n` is the least `K_b` with
  `16n³ ≤ (3/2)^(K_b)`; `graeffeSteps n η` is the least `k` with
  `8n/η ≤ 2^k`, proved to be the least `k` with `2^k η ≥ 8n` for `η > 0` (the
  definition of Appendix A). `doublingExponent` doubles `1, 2, 4, …` until
  `16n³` is reached; `graeffeDoubling` doubles `R = 1, 2, 4, …` and compares
  `Rη` with `8n`; both are proved to return these least exponents.
* `F : ℝ → ℝ` is always an arbitrary real function. Wherever the paper uses
  Lemma 2.1 for the spectral function `F(t) = Σ_j j λ_j(T + tX)`, the Lean
  statements instead take the conclusions of Lemma 2.1 as explicit premises:
  `ConvexOn ℝ Set.univ F`, and the secant bounds (9),
  `n(n+1)/2 ≤ secant F u v ≤ n²(n+1)/2` for all `u < v`.

## Algorithm 2 as a transcript

An oracle is any function `O : ℕ → ℝ → ℝ → ℝ`; request number `i` (counted
from 0 over the whole run) at point `x` with requested absolute error `τ`
receives the reply `O i x τ`. Since the algorithm is deterministic, every
adaptive reply strategy is such a function. A `Query` records point,
tolerance and reply.

`alg2Run O n δ` is Algorithm 2 (p. 17), literally:

1. `t = h = δ/(2n)`; three requests at `t-h, t, t+h` with tolerance `h/256`;
   return if `Ŝ_h(t) + 1/64 < 1/2`.
2. For `j = 0, …, K-1`: `h ← (1/2 - θ)h`; seven requests with tolerance
   `2θh/256` at the points of `S_h^(θ)(t-h)` and `S_h^(θ)(t+h)` (the point `t`
   serves both); compute both estimates from the replies; move to `t-h` if
   the left estimate is at most the right one (ties go left), otherwise to
   `t+h`; one request at the new center; compute `Ŝ_h(t)` from that reply and
   the two replies already received at the new center `∓ h`; return if
   `Ŝ_h(t) + 1/64 < 1/2`.

The result records the final state, the number of refinements, whether a
`return` statement was executed, and the full request log.
`alg2State O n δ j` is the state after `j` loop passes without tests.

`Algorithm2Certificate.run`: for all `n ≥ 1`, `δ > 0`, `F` convex with (9),
and every oracle `O` such that every request `q` in the log of
`alg2Run O n δ` satisfies `|q.reply - F q.point| ≤ q.tol`, the run satisfies
all fields of `Algorithm2Outcome`: it returns after at most `K` refinements,
at the first successful test; `h_j = (1/2-θ)^j δ/(2n)`; all windows are
nested and lie in `[0, δ/n]`; the initial endpoint variation is below `n³`;
(36) holds along the run, hence the iterated bound; if `K` refinements are
performed, the endpoint variation is below `1/8`; the returned test has error
at most `1/64`; the returned `(t, h)` satisfies (37), `S_h(t) < 1/2` and
`h > δ/(128n⁴)`, and also `h ≤ δ/(2n)` (hence `h < 1` for `δ < 1/2`),
`0 ≤ t`, `n t ≤ δ`; every request lies in `[0, δ/n]` with a tolerance above
`δ/(2¹⁶Kn⁴)` (40) and at most `δ/(512n)` (hence below `1` for `δ < 1/2`); the log has
exactly `3 + 8j` entries after `j` refinements, so at most `3 + 8K`; and
`h²/(2²⁰n⁴) > 2⁻³⁴δ²/n¹²`. The paper assumes `n ≥ 2` and `δ < 1/2`; these
are not needed for these conclusions. `premises_satisfiable` shows that the
premises hold for a linear `F` and the exact oracle, for every `n ≥ 1` and
`δ > 0`. `main_bound_form` is the second inequality of (5):
`2⁻³⁴δ²n⁻¹² ≥ 2⁻³⁴(δ/n)¹²` for `n ≥ 1` and `0 < δ < 1`.

## Theorem 1.1 (p. 2, proof p. 20)

Formalized: the scalar facts the proof uses about Algorithm 2 — the returned
`t` lies in `[0, δ/n]` with `nt ≤ δ`; at most `3 + 8K` requests, all at points
of `[0, δ/n]` with accuracies `δ/(2¹⁶Kn⁴) < ε < 1` for `δ < 1/2`, i.e. (40)
and `ε < 1` (from the bound `δ/(512n)`); `K` is found by doubling; `h ≤ δ/(2n) < 1` and
`h²/(2²⁰n⁴) > 2⁻³⁴δ²n⁻¹²`, which Proposition 3.1 turns into the gap bound;
and the second inequality of (5). Not formalized: `‖D‖₂ ≤ δ` and the gap
bound as matrix statements, the oracle of Lemma 4.3 and that the procedure
of Lemma 4.3 / Appendix A, applied to `F(t) = Σ_j jλ_j(T+tX)`, produces
replies meeting the error premise, the model of computation, and every
operation count, including `O(n[1+log(n/δ)]³)`.

## Other components

* `endpoint` (pp. 6, 16–17): for convex `F` and `h > 0`: `S_h(t) ≥ 0`; for
  `0 < θ ≤ 1/2`: `S_h^(θ)(t) ≥ 0` and (34). For `0 < θ ≤ 1/4`, `h > 0` and
  `h' = (1/2-θ)h`: the candidate windows are `[t-(1-2θ)h, t]` and
  `[t, t+(1-2θ)h]`; the seven requested points lie in `[t-h, t+h]`; the two
  child variations sum to at most the parent one, hence (35); four values
  within `2θh/256` give an estimate within `1/64`; ties go left; and (36) for
  one refinement with arbitrary replies within `2θh'/256`.
* `basicSelector` (pp. 14–16): the weight inequality of the proof of
  Lemma 4.1 for all `t, x` and `h > 0`, with equality at `x = t - h/4`;
  (29) for every convex `F`, proved directly from three three-point convexity
  inequalities (the paper's proof uses the second-derivative measure); the
  estimate error `1/64` for tolerance `r/256`; (30) for one refinement of
  Algorithm 1 with five arbitrary replies within `(h/4)/256` and ties to the
  left; `S_h(t) < n³` from (9); `K_b` least and `= ⌈log_(3/2)(16n³)⌉`;
  `(2/3)^(K_b) n³ ≤ 1/16`; for every real sequence with `s₀ < n³` and
  `s_(j+1) ≤ (2/3)s_j + 1/32`: `s_j < (2/3)^j n³ + (1/32)Σ_(l<j)(2/3)^l`, the
  sum term below `3/32`, `s_(K_b) < 5/32`; `5/32 + 2/64 < 1/2`;
  `3 + 5j ≤ 3 + 5K_b` for `j ≤ K_b`; and (32) for every radius
  `(δ/(2n))4^(-j)`, `j ≤ K_b`, `n ≥ 1`, `δ > 0`, with `α = log_(3/2) 4`;
  and, as stated in the proof of Theorem 4.1, every such radius is at most
  `δ/(2n) < 1` for `δ < 1/2`.
* `graeffe` and `coefficients` (p. 27): for every `n`, all real roots
  `r : Fin n → ℝ` and every `k`: the coefficient split reconstructs the
  polynomial, one Graeffe step maps `∏(X + r_i)` to `∏(X + r_i²)`, the `k`-th
  iterate gives `∏(X + r_i^(2^k))`, and the descending coefficients are the
  elementary symmetric sums. For positive nonincreasing roots:
  positivity, `p_j ≤ e_j ≤ C(n,j) p_j ≤ 2ⁿ p_j` for `j ≤ n`, and
  `r_i^(2^k)/2ⁿ ≤ e_(i+1)/e_i ≤ 2ⁿ r_i^(2^k)` (Lean index `i` is the
  paper's `j = i+1`).
* `rootExtraction` (pp. 19, 27): `e_j` is read off the actual Graeffe iterate.
  For positive nonincreasing roots: (43) with `R = 2^k` and real powers;
  `x^(1/2^k)` equals `k` successive square roots for `x ≥ 0`;
  `2^x - 1 ≤ x` on `[0, 1]`; `|r̂_j - r_j| ≤ 4n/R` when `r_j < 4` and `n ≤ R`;
  for `η > 0`, `k` is the least integer with `2^k η ≥ 8n` and doubling `R`
  from `1` with any budget of at least `k` steps returns it; for `n ≥ 1`,
  `0 < η < 1`: `8n/η ≤ R < 16n/η`, `n ≤ R`, `4n/R ≤ η/2`; errors
  `ε/(2Σj)` in every `λ_j` give error `≤ ε` in `Σ_j jλ_j` (any `ε ≥ 0`), and
  errors `η` give `≤ n(n+1)η/2`. The pipeline: for `n ≥ 1`, roots in `(0, 4)`
  in nonincreasing order and `0 < ε < 1`, with `η = ε/Σj` and `k` chosen by
  doubling, `λ_j = r_(n+1-j) - 2` is nondecreasing, every
  `λ̂_j = r̂_(n+1-j) - 2` (with `r̂` from `k` square roots of
  `e_(n+1-j)/e_(n-j)`) is within `η/2` of `λ_j` (index-wise matching), and
  `|Σ_j jλ̂_j - Σ_j jλ_j| ≤ (n(n+1)/2)(η/2) ≤ ε`. The facts
  `r_(n+1-j) = 2 + λ_j(A)` and `r_j ∈ (0, 4)` are premises.
* `continuant` (p. 27): for every commutative ring, all sequences `a, b, c`
  and every `k`, the determinant of the `k × k` tridiagonal matrix with
  diagonal `a`, superdiagonal `b` and subdiagonal `c` is the continuant
  (`Q_0 = 1`, `Q_1 = a_0`, `Q_(k+2) = a_(k+1) Q_(k+1) - b_k c_k Q_k`). For
  every `n` and every real `A : Fin n × Fin n → ℝ` whose entries vanish more
  than one step off the diagonal, `det(zI + 2I + A)` (a polynomial in `z`)
  equals `P_n` for the recurrence of Appendix A, `P_0 = 1`,
  `P_1 = z + 2 + a_1`, `P_i = (z + 2 + a_i)P_(i-1) - c_(i-1)P_(i-2)` for
  `2 ≤ i ≤ n`, with `a_i = A_(i,i)` and `c_i = A_(i,i+1) A_(i+1,i)` (1-based);
  for symmetric `A`, `c_i = A_(i,i+1)²`. In Lean, `charRecurrence A` has
  exactly these three cases (index `i + 2` uses the 0-based entries
  `A_(i+1,i+1)` and `A_(i,i+1) A_(i+1,i)`); it is defined for every index but
  only its terms up to `n` enter `P_n`.
* `localConstants` (pp. 9–13, 19): real inequalities and identities of the
  proofs of Lemma 3.1 (`n(1/(2√n))² = 1/4`, `√(3/8) > 1/2`,
  `τ = 4√(nγ) ≤ 1/(4√n)` for `0 ≤ γ ≤ 1/(256n²)`, the bounds in cases (a)
  and (c) of Step 3 in terms of real parameters, `5nγ/τ² = 5/16 < 1/2`, and
  Step 4: `2√n(γ/2 + √2τ) ≤ 4√nτ = 16n√γ`), of Lemma 3.2 (`3√2` times the
  root of a sum of two squares each at most `(16n√γ)²` is at most `96n√γ`)
  and of Proposition 3.1 (`0 < h ≤ 1` gives `0 < γ ≤ 1/(256n²)`; the quotient
  in (27) is (13); (28) at three points gives `S_h(t) ≥ S_h^aux(t) - (4n/h)N`
  for arbitrary real functions `F, G` and reals `n, N`; at
  `γ = h²/(2²⁰n⁴)`, `1 - 384n²√γ/h = 5/8 > 1/2`; and the complete scalar
  chain from `S^aux ≥ 1`, `N ≤ 96n√γ` and the three error bounds to
  `S_h(t) > 1/2`); and `h > δ/(128n⁴)` gives `h²/(2²⁰n⁴) > 2⁻³⁴δ²/n¹²`.
* `wronskian` (p. 10): for real sequences `d, β, a, b` on coordinates
  `1, …, n` with `β_0 = 0` satisfying the coordinate equations of Step 2
  with eigenvalues `λ, μ`: (22) for every `i ≤ n`; if moreover `a, b` are
  orthonormal on `1, …, n`, then `|Σ_(j≤i) a_j b_j| ≤ 1/2`, and with
  `|λ - μ| ≤ γ`, `|β_i| |det(r_i, r_(i+1))| ≤ γ/2`.

## Not formalized

* All spectral theory: the spectral function and its properties (Lemma 2.1,
  (7)–(12), (14), (15): the variational representation, Hellmann–Feynman and
  second-derivative formulas), Remark 1.1 (reduction to real symmetric
  matrices), and the identification of the abstract `F` with
  `Σ_j j λ_j(T + tX)`.
* Section 3 as matrix statements: the existence of the cut and of the
  localized vectors in Lemma 3.1 (Steps 1, 3 and 4 beyond the listed scalar
  facts, including the projector and commutator estimates), the auxiliary
  matrix and its nuclear-norm bound in Lemma 3.2, the supporting-slope
  argument for (27), the operator–nuclear duality (28), and
  Proposition 3.1 itself. The Wronskian identity is formalized for the
  coordinate recurrence, not derived from a matrix–vector product.
* Consequently the gap conclusions of Theorems 4.1 and 4.2 (`gap(T + D) > …`)
  and `‖tX‖₂ = nt`; the Lean statements stop at `S_h(t) < 1/2`, the radius,
  `0 ≤ t ≤ δ/n`, `nt ≤ δ` and the scalar bound on `h²/(2²⁰n⁴)`.
* The transcript of Algorithm 1 and Theorem 4.1 as a statement about a run;
  only one refinement and the constants of its proof are formalized. The
  measure representation used in the proof of Lemma 4.1 is not formalized.
* The oracle of Lemma 4.3 and Appendix A as an algorithm: that the procedure
  of Lemma 4.3 / Appendix A, applied to `F(t) = Σ_j jλ_j(T+tX)`, produces
  replies meeting the error premise, the arithmetic model, all cost and
  complexity bounds (including `O(n[1+log(n/ε)]²)` of Lemma 4.3, the total
  `O(n[1+log(n/δ)]³)` of Theorem 1.1 and `ε_min` beyond (40)),
  `P(z) = ∏(z + r_j)` (which needs the spectral theorem), the complex
  Hermitian case with `c_i = (Re A_(i,i+1))² + (Im A_(i,i+1))²`, balanced
  product trees, fast Fourier transforms and roots of unity, and bit
  complexity. The request count is the length of the defined log, not a cost.
* The numerical illustrations of Section 5 and the examples.
