# Paper results and their evidence

This map follows [the paper source](../paper/main.tex) and its two included fragments in TeX order, with page numbers of [the PDF](../paper/main.pdf). Theorems, propositions, lemmas, definitions, examples and remarks each have their own counter within each section; the two algorithms are numbered globally. There are 23 numbered results: three theorems, one proposition, six lemmas, one definition, six examples, four remarks and two algorithms. Sections 5 and 6 and Appendix A contain no numbered result; the supporting anchors below cover equations and Appendix A. Equation numbers are those of the paper. [mapping.json](mapping.json) is the machine-readable form of this map, and [build_and_check.py](build_and_check.py) checks it against the sources.

| Coverage | Meaning | Results |
| --- | --- | --- |
| Formalized in full | Every assertion of the result is a Lean theorem, for every real function F that has the properties the paper takes from Lemma 2.1 (convexity and, where used, the secant bounds (9)); these enter as explicit premises, and Lemma 2.1 itself is not formalized | 4 |
| Formalized scalar part only | The scalar, finite or algebraic steps listed for the entry are Lean theorems; the statement itself is a written proof | 9 |
| Exact finite cross-check only | No Lean theorem; standard-library programs check the listed claims exactly on finite ranges or fixed instances | 7 |
| Written proof only | Neither a Lean theorem nor an exact check is assigned | 3 |

| Result | Label | Page | Title | Coverage |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | 2 | Main theorem | Formalized scalar part only |
| Remark 1.1 | `rem:real` | 4 | Reduction to real symmetric matrices | Written proof only |
| Example 2.1 | `ex:tails` | 5 | Tail sums and spectral spread | Exact finite cross-check only |
| Lemma 2.1 | `lem:convex` | 5 | Properties of the spectral function | Exact finite cross-check only |
| Definition 2.1 | `def:defect` | 6 | Centered slope variation | Formalized in full |
| Example 2.2 | `ex:collision` | 7 | A collision produces a corner | Exact finite cross-check only |
| Example 2.3 | `ex:tridiagonal-defect` | 7 | A tridiagonal matrix with avoided crossings | Exact finite cross-check only |
| Proposition 3.1 | `prop:bridge` | 8 | Local gap certificate | Formalized scalar part only |
| Example 3.1 | `ex:localization` | 9 | An illustrative example of a small-leakage cut | Exact finite cross-check only |
| Lemma 3.1 | `lem:localization` | 9 | Spatially separated approximate eigenvectors | Formalized scalar part only |
| Example 3.2 | `rem:localization-example` | 11 | Identifying the small-leakage cut in Example 3.1 | Exact finite cross-check only |
| Remark 3.1 | `rem:tridiagonal-localization` | 12 | Role of the tridiagonal structure | Written proof only |
| Lemma 3.2 | `lem:auxiliary` | 12 | A nearby matrix with large slope variation | Formalized scalar part only |
| Algorithm 1 | `alg:selection-basic` | 14 | Basic selection of a perturbation parameter | Formalized scalar part only |
| Example 4.1 | `ex:selection` | 14 | One step of interval selection | Exact finite cross-check only |
| Lemma 4.1 | `lem:defect-contraction`, `lem:inexact-contraction` | 15 | Contraction of centered slope variation | Formalized in full |
| Theorem 4.1 | `thm:selection-basic` | 15 | Basic iteration bound and certified scale | Formalized scalar part only |
| Remark 4.1 | `rem:basic-selection-scale` | 16 | A lower bound on the window radius | Formalized scalar part only |
| Algorithm 2 | `alg:selection` | 17 | Improved selection of a separating perturbation | Formalized in full |
| Lemma 4.2 | `lem:potential-contraction`, `lem:potential-inexact` | 17 | Contraction of endpoint slope variation | Formalized in full |
| Theorem 4.2 | `thm:selection` | 18 | Improved constructive spectral separation | Formalized scalar part only |
| Remark 4.2 | `rem:selection-scale` | 19 | Improvement over the basic selector | Written proof only |
| Lemma 4.3 | `lem:oracle` | 19 | Spectral-function oracle | Formalized scalar part only |

Supporting anchors are equations and the appendix whose content is formalized or checked separately from the numbered result that contains or uses them.

| Anchor | Label | Page | Title |
| --- | --- | --- | --- |
| (5) | `eq:main` | 2 | The two forms of the gap bound in Theorem 1.1 |
| (22) | `eq:wronskian` | 10 | The discrete Wronskian identity |
| (28) | `eq:nuclear` | 13 | The operator-nuclear duality bound |
| (33) | `eq:endpoint-slope` | 16 | Endpoint slope variation |
| (34) | `eq:potential-controls-S` | 17 | Endpoint slopes control the centered slope variation |
| (40) | `eq:minimum-oracle-accuracy` | 20 | The smallest requested accuracy |
| Appendix A | `app:oracle` | 27 | The spectral-function oracle: algebraic details |
| (43) | `eq:graeffe` | 27 | The Graeffe ratio bound |

No exact check establishes a statement quantified over all matrices, all functions or all parameters, and no numerical illustration is used in a proof. The Lean definitions of the slope variations (13) and (33) are `KE02.centeredVariation` and `KE02.endpointVariation`, and Algorithm 2 is the transcript `KE02.alg2Run` of an arbitrary reply function; see [SCOPE.md](../lean/SCOPE.md) for every definition.

## The Lean certificate

The aggregate theorem is `KE02.coreCertificate : KE02.CoreCertificate` in [lean/KE02.lean](../lean/KE02.lean); its kernel dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`. The proposition has nine components, each a structure of universally quantified statements with all premises explicit:

- `KE02.CoreCertificate.endpoint` : `KE02.EndpointCertificate` ([EndpointStatement.lean](../lean/KE02/EndpointStatement.lean)), proved by `KE02.endpointCertificate` in [EndpointProof.lean](../lean/KE02/EndpointProof.lean). Inequality (34), the nonnegativity of (13) and (33) for convex F, and Lemma 4.2 with its proof ingredients, for every 0 < θ ≤ 1/4.
- `KE02.CoreCertificate.algorithm2` : `KE02.Algorithm2Certificate` ([Algorithm2Statement.lean](../lean/KE02/Algorithm2Statement.lean)), proved by `KE02.algorithm2Certificate` in [Algorithm2Proof.lean](../lean/KE02/Algorithm2Proof.lean). K, θ and the constants of the proof of Theorem 4.2, and the run of Algorithm 2 on an arbitrary reply function whose replies meet the requested accuracies: Theorem 4.2 without Proposition 3.1.
- `KE02.CoreCertificate.basicSelector` : `KE02.BasicSelectorCertificate` ([BasicSelectorStatement.lean](../lean/KE02/BasicSelectorStatement.lean)), proved by `KE02.basicSelectorCertificate` in [BasicSelectorProof.lean](../lean/KE02/BasicSelectorProof.lean). Lemma 4.1, one refinement of Algorithm 1, and the constants and scalar recursion of Theorem 4.1 and Remark 4.1.
- `KE02.CoreCertificate.graeffe` : `KE02.GraeffeCertificate` ([GraeffeStatement.lean](../lean/KE02/GraeffeStatement.lean)), proved by `KE02.graeffeCertificate` in [GraeffeUniversal.lean](../lean/KE02/GraeffeUniversal.lean). Appendix A: the even/odd split, one Graeffe step and its iterates, for all real roots.
- `KE02.CoreCertificate.coefficients` : `KE02.CoefficientCertificate` ([CoefficientStatement.lean](../lean/KE02/CoefficientStatement.lean)), proved by `KE02.coefficientCertificate` in [CoefficientProof.lean](../lean/KE02/CoefficientProof.lean). Appendix A: the coefficients e\_j of ∏(X + r\_i^(2^k)), their positivity, p\_j ≤ e\_j ≤ 2^n p\_j and the ratio bounds.
- `KE02.CoreCertificate.rootExtraction` : `KE02.RootExtractionCertificate` ([RootExtractionStatement.lean](../lean/KE02/RootExtractionStatement.lean)), proved by `KE02.rootExtractionCertificate` in [RootExtractionProof.lean](../lean/KE02/RootExtractionProof.lean). Appendix A and the remark after Lemma 4.3: (43), the R-th root as k square roots, the error 4n/R ≤ η/2, the choice of k by doubling, and the index-wise matching with weighted error at most ε.
- `KE02.CoreCertificate.continuant` : `KE02.ContinuantCertificate` ([ContinuantStatement.lean](../lean/KE02/ContinuantStatement.lean)), proved by `KE02.continuantCertificate` in [ContinuantProof.lean](../lean/KE02/ContinuantProof.lean). Appendix A: the determinant of a tridiagonal matrix is the continuant, and the recurrence ends in det(zI + 2I + A).
- `KE02.CoreCertificate.localConstants` : `KE02.LocalConstantsCertificate` ([LocalConstantsStatement.lean](../lean/KE02/LocalConstantsStatement.lean)), proved by `KE02.localConstantsCertificate` in [LocalConstantsProof.lean](../lean/KE02/LocalConstantsProof.lean). The real-number inequalities and identities of the proofs of Lemma 3.1, Lemma 3.2 and Proposition 3.1, and the chain ending in 2^-34.
- `KE02.CoreCertificate.wronskian` : `KE02.WronskianCertificate` ([WronskianStatement.lean](../lean/KE02/WronskianStatement.lean)), proved by `KE02.wronskianCertificate` in [WronskianProof.lean](../lean/KE02/WronskianProof.lean). The discrete Wronskian identity (22) for the coordinate recurrence and the two bounds of Step 2 of the proof of Lemma 3.1.

The field `KE02.Algorithm2Certificate.run` concludes `KE02.Algorithm2Outcome`, a structure of 26 statements about the run, all proved by `KE02.algorithm2_outcome`.

## 1. Introduction

Theorem 1.1 combines Theorem 4.2 with Lemma 4.3. The Lean certificate contains the scalar facts that its proof uses about Algorithm 2; the matrix conclusions and the cost bound are written proofs.

**Theorem 1.1** (`thm:main`, page 2). Main theorem. Coverage: formalized scalar part only.

Covered: The scalar facts its proof uses about Algorithm 2, for every n ≥ 1, δ > 0, convex F with (9) and every reply function that meets the requested accuracies: the run returns t with [t - h, t + h] ⊆ [0, δ/n], so 0 ≤ t and nt ≤ δ; it makes at most 3 + 8K requests, all at points of [0, δ/n] with accuracies δ/(2^16 K n^4) < ε ≤ δ/(512n), hence ε < 1 for δ < 1/2; K is found by doubling; h ≤ δ/(2n) < 1 and h^2/(2^20 n^4) > 2^-34 δ^2 n^-12, which Proposition 3.1 turns into the gap bound; and the second inequality of (5).

Not covered: ‖D‖\_2 ≤ δ and the gap bound as matrix statements, which need Proposition 3.1 and spectral theory; that F is the spectral function of T + tX, and Lemma 2.1; that the oracle of Lemma 4.3 and Appendix A produces replies meeting the accuracy premise; the model of computation and every operation count, including O(n[1 + log(n/δ)]^3).

Lean fields:

- `KE02.Algorithm2Certificate.K_doubling`, proved by `KE02.alg2K_doubling`: Repeated doubling from 1 returns K.
- `KE02.Algorithm2Certificate.run`, proved by `KE02.algorithm2_outcome`: For every n ≥ 1, δ > 0, convex F satisfying (9) and every reply function whose replies to the requests of the run are within the requested errors, the run of Algorithm 2 satisfies every field of KE02.Algorithm2Outcome.
- `KE02.Algorithm2Outcome.returns`, proved by `KE02.algorithm2_outcome`: The run executes a return statement.
- `KE02.Algorithm2Outcome.window`, proved by `KE02.algorithm2_outcome`: (37), middle part: [t - h, t + h] ⊆ [0, δ/n].
- `KE02.Algorithm2Outcome.budget`, proved by `KE02.algorithm2_outcome`: 0 ≤ t and nt ≤ δ, the scalar part of ‖D‖\_2 ≤ δ.
- `KE02.Algorithm2Outcome.radius_upper`, proved by `KE02.algorithm2_outcome`: h ≤ δ/(2n).
- `KE02.Algorithm2Outcome.radius_lt_one`, proved by `KE02.algorithm2_outcome`: For δ < 1/2, h < 1, as Proposition 3.1 requires.
- `KE02.Algorithm2Outcome.queries_inside`, proved by `KE02.algorithm2_outcome`: Every request lies in [0, δ/n] and has a positive tolerance.
- `KE02.Algorithm2Outcome.tolerance_upper`, proved by `KE02.algorithm2_outcome`: Every requested accuracy is at most δ/(512n).
- `KE02.Algorithm2Outcome.tolerance_lt_one`, proved by `KE02.algorithm2_outcome`: For δ < 1/2 every requested accuracy is below 1.
- `KE02.Algorithm2Outcome.min_accuracy`, proved by `KE02.algorithm2_outcome`: (40): every requested accuracy exceeds δ/(2^16 K n^4).
- `KE02.Algorithm2Outcome.calls_le`, proved by `KE02.algorithm2_outcome`: At most 3 + 8K requests.
- `KE02.Algorithm2Outcome.gap_scale`, proved by `KE02.algorithm2_outcome`: h^2/(2^20 n^4) > 2^-34 δ^2 n^-12 at the returned radius: the scalar step of (38).
- `KE02.LocalConstantsCertificate.gap_chain`, proved by `KE02.gap_chain`: h > δ/(128n^4) gives h^2/(2^20 n^4) > 2^-34 δ^2 n^-12.
- `KE02.Algorithm2Certificate.main_bound_form`, proved by `KE02.main_bound_form`: The second inequality of (5): 2^-34 δ^2 n^-12 ≥ 2^-34 (δ/n)^12 for n ≥ 1 and 0 < δ < 1.

Exact checks:

- `verification/core/check_constants.py:fam_c12` (family C12)
- `verification/core/check_constants.py:fam_c13` (family C13)

Numerical illustration, not part of any proof: item `adaptive` in Section 5 below.

**Remark 1.1** (`rem:real`, page 4). Reduction to real symmetric matrices. Coverage: written proof only.

Covered: No Lean declaration or exact check is assigned.

Not covered: The diagonal unitary gauge S with S\*TS real symmetric and S\*XS = X, and the resulting invariance of eigenvalues, gaps and norms.

**Equation (5)** (`eq:main`, page 2). The two forms of the gap bound in Theorem 1.1.

Covered: 2^-34 δ^2 n^-12 ≥ 2^-34 (δ/n)^12 for n ≥ 1 and 0 < δ < 1.

Not covered: The gap bound itself.

Lean fields:

- `KE02.Algorithm2Certificate.main_bound_form`, proved by `KE02.main_bound_form`: The second inequality of (5): 2^-34 δ^2 n^-12 ≥ 2^-34 (δ/n)^12 for n ≥ 1 and 0 < δ < 1.

Exact checks:

- `verification/core/check_constants.py:fam_c12` (family C12)

## 2. The convex spectral function and its slope variation

Lemma 2.1 is not formalized. Wherever a Lean statement needs its conclusions, convexity of F and the secant bounds (9) are explicit premises on an arbitrary real function F.

**Example 2.1** (`ex:tails`, page 5). Tail sums and spectral spread. Coverage: exact finite cross-check only.

Covered: The tail-sum identity (10), of which the displayed decomposition is the case n = 3, and the identity (8), on exact sorted spectra with n ≤ 9.

Not covered: The interpretation of the slope variation.

Exact checks:

- `verification/core/check_constants.py:fam_c01` (family C01)

**Lemma 2.1** (`lem:convex`, page 5). Properties of the spectral function. Coverage: exact finite cross-check only.

Covered: Σj = n(n+1)/2 and Σjn = n^2(n+1)/2, the identities (8) and (10) on exact sorted spectra, and (9), midpoint convexity and 0 ≤ S\_h(t) ≤ (n^3 - n)/2 on 400 exact diagonal instances.

Not covered: The lemma for every Hermitian T: monotonicity, convexity, the secant bounds (9) and the variational representation (10) from Ky Fan's maximum principle. Wherever Lean uses these properties, convexity of F and (9) are explicit premises.

Exact checks:

- `verification/core/check_constants.py:fam_c01` (family C01)

**Definition 2.1** (`def:defect`, page 6). Centered slope variation. Coverage: formalized in full.

Covered: (13) is the Lean definition KE02.centeredVariation, and S\_h(t) ≥ 0 is proved for every convex F and h > 0.

Not covered: Convexity of the spectral function F, Lemma 2.1, which enters as a premise.

Lean fields:

- `KE02.EndpointCertificate.centered_nonneg`, proved by `KE02.centered_nonneg`: For convex F and h > 0: S\_h(t) ≥ 0, the inequality in (13).

Exact checks:

- `verification/core/check_constants.py:fam_c01` (family C01)
- `verification/core/check_constants.py:fam_c02` (family C02)

**Example 2.2** (`ex:collision`, page 7). A collision produces a corner. Coverage: exact finite cross-check only.

Covered: (16) and (17) exactly: the closed form of F and the triangular peak of S\_h for several h on a grid of centres.

Not covered: Figure 1, which is a plot.

Exact checks:

- `verification/core/check_constants.py:fam_c02` (family C02)

**Example 2.3** (`ex:tridiagonal-defect`, page 7). A tridiagonal matrix with avoided crossings. Coverage: exact finite cross-check only.

Covered: The crossing points 0.06, 0.08 and 0.10 of the diagonal branches, and an exact bracket of S\_0.006(0.08) by Sturm bisection, which rounds to the value 1.8541 stated for Figure 2.

Not covered: The plotted curves of Figure 2.

Exact checks:

- `verification/core/check_constants.py:fam_c02` (family C02)

## 3. Small slope variation certifies a spectral gap

Section 3 is formalized only through the real inequalities and identities of its proofs and the discrete Wronskian identity for the coordinate recurrence; no matrix statement of the section is a Lean theorem.

**Proposition 3.1** (`prop:bridge`, page 8). Local gap certificate. Coverage: formalized scalar part only.

Covered: The scalar steps of the proof: 0 < h ≤ 1 gives 0 < γ ≤ 1/(256n^2) for γ = h^2/(2^20 n^4); the quotient in (27) is (13); (28) at t - h, t and t + h gives S\_h(t) ≥ S\_h^aux(t) - (4n/h)N for arbitrary real functions; 1 - 384n^2 √γ/h = 5/8 > 1/2; and the complete scalar chain from S^aux ≥ 1, N ≤ 96n√γ and the three bounds |F - G| ≤ nN to S\_h(t) > 1/2.

Not covered: The proposition itself: the localized vectors and the auxiliary matrix of Lemmas 3.1 and 3.2, the operator-nuclear duality (28), and the conclusion gap(H(t)) > h^2/(2^20 n^4).

Lean fields:

- `KE02.LocalConstantsCertificate.gamma_range`, proved by `KE02.gamma_range`: Proposition 3.1: 0 < h ≤ 1 gives 0 < γ ≤ 1/(256n^2) for γ = h^2/(2^20 n^4).
- `KE02.LocalConstantsCertificate.aux_variation`, proved by `KE02.aux_variation`: The quotient in (27) is the centred slope variation (13) of the auxiliary function.
- `KE02.LocalConstantsCertificate.transfer`, proved by `KE02.transfer`: (28) at t - h, t and t + h gives S\_h(t) ≥ S\_h^aux(t) - (4n/h)N, for arbitrary real functions F, G and reals n, N.
- `KE02.LocalConstantsCertificate.constant`, proved by `KE02.prop31_constant`: 1 - 384n^2 √γ/h = 5/8 > 1/2 at γ = h^2/(2^20 n^4), with 384/1024 = 3/8.
- `KE02.LocalConstantsCertificate.chain`, proved by `KE02.prop31_chain`: The scalar chain of Proposition 3.1: S^aux ≥ 1, N ≤ 96n√γ and |F - G| ≤ nN at three points give S\_h(t) > 1/2.

Exact checks:

- `verification/core/check_constants.py:fam_c08` (family C08)

Numerical illustration, not part of any proof: item `adaptive` in Section 5 below.

**Example 3.1** (`ex:localization`, page 9). An illustrative example of a small-leakage cut. Coverage: exact finite cross-check only.

Covered: ‖H‖\_2 < 1 by row sums, nonzero couplings, and the two eigenvalues -5.173792·10^-6 and 4.739763·10^-6 to 10^-12, adjacent in the spectrum, with |λ - μ| < γ.

Not covered: The printed eigenvectors u\_1, u\_2, v\_1, v\_2, the residuals and the X-response 5.0000.

Exact checks:

- `verification/core/check_constants.py:fam_c02` (family C02)

**Lemma 3.1** (`lem:localization`, page 9). Spatially separated approximate eigenvectors. Coverage: formalized scalar part only.

Covered: The discrete Wronskian identity (22) for the coordinate recurrence and the two bounds of Step 2; the real inequalities of Steps 1, 3 and 4: n(1/(2√n))^2 = 1/4, √(3/8) > 1/2, τ ≤ 1/(4√n), the bounds of cases (a) and (c), 5nγ/τ^2 = 5/16 < 1/2 and 2√n(γ/2 + √2 τ) ≤ 16n√γ.

Not covered: The existence of the cut and of the localized vectors: the choice of p and q, the path argument over large and small rows, the projector and commutator estimates as matrix statements and the X-response bound. The Wronskian identity is formalized for the coordinate recurrence, not derived from a matrix-vector product.

Lean fields:

- `KE02.LocalConstantsCertificate.discarded_rows`, proved by `KE02.discarded_rows`: Lemma 3.1, Step 1: n(1/(2√n))^2 = 1/4.
- `KE02.LocalConstantsCertificate.direction_gap`, proved by `KE02.direction_gap`: (21): √(3/8) > 1/2.
- `KE02.LocalConstantsCertificate.tau_le`, proved by `KE02.tau_le`: Step 3: τ = 4√(nγ) ≤ 1/(4√n) for 0 ≤ γ ≤ 1/(256n^2).
- `KE02.LocalConstantsCertificate.case_a`, proved by `KE02.case_a`: Step 3, case (a): γ/(2τ^2) ≤ 5γ/τ^2.
- `KE02.LocalConstantsCertificate.case_c`, proved by `KE02.case_c`: Step 3, case (c): 2γ/(AB) + γρ/(2B) ≤ 5γ/τ^2 for τ < A, τ < B and 0 ≤ ρ ≤ τ ≤ 1.
- `KE02.LocalConstantsCertificate.total_change`, proved by `KE02.total_change`: Step 3: 5nγ/τ^2 = 5/16 < 1/2.
- `KE02.LocalConstantsCertificate.truncation`, proved by `KE02.truncation`: Step 4: 2√n(γ/2 + √2 τ) ≤ 4√n τ = 16n√γ.
- `KE02.WronskianCertificate.identity`, proved by `KE02.wronskian_identity`: (22) for every i ≤ n, for real sequences satisfying the coordinate equations of Step 2 with β\_0 = 0.
- `KE02.WronskianCertificate.partial_inner`, proved by `KE02.partial_inner`: Step 2: |Σ\_(j≤i) (u\_1)\_j (u\_2)\_j| ≤ 1/2 for orthonormal u\_1, u\_2.
- `KE02.WronskianCertificate.bound`, proved by `KE02.wronskian_bound`: Step 2: |β\_i| |det(r\_i, r\_(i+1))| ≤ γ/2 when |λ - μ| ≤ γ.

Exact checks:

- `verification/core/check_constants.py:fam_c03` (family C03)
- `verification/core/check_constants.py:fam_c04` (family C04)
- `verification/core/check_constants.py:fam_c05` (family C05)
- `verification/core/check_constants.py:fam_c06` (family C06)

**Example 3.2** (`rem:localization-example`, page 11). Identifying the small-leakage cut in Example 3.1. Coverage: exact finite cross-check only.

Covered: τ = 4√(nγ) rounds to 0.0358 for n = 8 and γ = 10^-5, and the column L\_k ≤ τ of the table agrees with the printed values L\_k.

Not covered: The printed matrix entries, determinants and leakages L\_k themselves are not recomputed.

Exact checks:

- `verification/core/check_constants.py:fam_c02` (family C02)

**Remark 3.1** (`rem:tridiagonal-localization`, page 12). Role of the tridiagonal structure. Coverage: written proof only.

Covered: No Lean declaration or exact check is assigned.

Not covered: Where the tridiagonal assumption enters the proof.

**Lemma 3.2** (`lem:auxiliary`, page 12). A nearby matrix with large slope variation. Coverage: formalized scalar part only.

Covered: 3√2 (a\_1^2 + a\_2^2)^(1/2) ≤ 96n√γ when 0 ≤ a\_i ≤ 16n√γ, and the identification of the quotient in (27) with (13).

Not covered: The auxiliary matrix H̃, the nuclear-norm bound (26) as a matrix statement and the supporting-slope argument for (27).

Lean fields:

- `KE02.LocalConstantsCertificate.nuclear`, proved by `KE02.nuclear`: Lemma 3.2, (26): 3√2 (a\_1^2 + a\_2^2)^(1/2) ≤ 96n√γ when 0 ≤ a\_i ≤ 16n√γ.
- `KE02.LocalConstantsCertificate.aux_variation`, proved by `KE02.aux_variation`: The quotient in (27) is the centred slope variation (13) of the auxiliary function.

Exact checks:

- `verification/core/check_constants.py:fam_c07` (family C07)

**Equation (22)** (`eq:wronskian`, page 10). The discrete Wronskian identity.

Covered: (22) for every i ≤ n and the two bounds of Step 2, for real sequences satisfying the coordinate equations.

Not covered: Its derivation from the matrix eigenvector equations.

Lean fields:

- `KE02.WronskianCertificate.identity`, proved by `KE02.wronskian_identity`: (22) for every i ≤ n, for real sequences satisfying the coordinate equations of Step 2 with β\_0 = 0.
- `KE02.WronskianCertificate.partial_inner`, proved by `KE02.partial_inner`: Step 2: |Σ\_(j≤i) (u\_1)\_j (u\_2)\_j| ≤ 1/2 for orthonormal u\_1, u\_2.
- `KE02.WronskianCertificate.bound`, proved by `KE02.wronskian_bound`: Step 2: |β\_i| |det(r\_i, r\_(i+1))| ≤ γ/2 when |λ - μ| ≤ γ.

Exact checks:

- `verification/core/check_constants.py:fam_c04` (family C04)

**Equation (28)** (`eq:nuclear`, page 13). The operator-nuclear duality bound.

Covered: Taken as a hypothesis at t - h, t and t + h, (28) gives S\_h(t) ≥ S\_h^aux(t) - (4n/h)N.

Not covered: (28) itself: the variational representation and operator-nuclear duality.

Lean fields:

- `KE02.LocalConstantsCertificate.transfer`, proved by `KE02.transfer`: (28) at t - h, t and t + h gives S\_h(t) ≥ S\_h^aux(t) - (4n/h)N, for arbitrary real functions F, G and reals n, N.

Exact checks:

- `verification/core/check_constants.py:fam_c08` (family C08)

## 4. The algorithm: adaptive selection of the perturbation parameter

Lemma 4.1, Algorithm 2 and Lemma 4.2 are formalized for every convex F (with (9) where the run is concerned). Theorem 4.2 is formalized except for (38) and the norm identity, which use Proposition 3.1 and spectral theory. Algorithm 1 and Theorem 4.1 are formalized for one refinement and through the constants and the scalar recursion of the proof. Lemma 4.3 is formalized through the algebra of Appendix A only.

**Algorithm 1** (`alg:selection-basic`, page 14). Basic selection of a perturbation parameter. Coverage: formalized scalar part only.

Covered: One refinement, with its five evaluation points, the tolerance (h/4)/256 and the selection with ties to the left, is the statement basicSelector.step; K\_b is the least natural number with (3/2)^(K\_b) ≥ 16n^3.

Not covered: The transcript of Algorithm 1 as a whole, the search for K\_b by repeated multiplication, and the claim that its last line is not reached (Theorem 4.1).

Lean fields:

- `KE02.BasicSelectorCertificate.step`, proved by `KE02.basic_step`: (30) for one refinement of Algorithm 1: five replies within (h/4)/256, the smaller computed child variation selected, ties to the left.
- `KE02.BasicSelectorCertificate.Kb_spec`, proved by `KE02.basicK_spec`: K\_b is the least natural number with (3/2)^(K\_b) ≥ 16n^3.
- `KE02.EndpointCertificate.ties_left`, proved by `KE02.selectCenter_tie`: The selection rule moves to t - h when the two computed estimates are equal.

Exact checks:

- `verification/core/check_constants.py:fam_c10` (family C10)
- `verification/core/check_constants.py:fam_c13` (family C13)

**Example 4.1** (`ex:selection`, page 14). One step of interval selection. Coverage: exact finite cross-check only.

Covered: S\_0.04(0.1) = 1, the window arithmetic and the vanishing of both child variations, exactly.

Not covered: The closing sentence about the selection rule in general.

Exact checks:

- `verification/core/check_constants.py:fam_c02` (family C02)

**Lemma 4.1** (`lem:defect-contraction`, `lem:inexact-contraction`, page 15). Contraction of centered slope variation. Coverage: formalized in full.

Covered: (29) for every convex F and h > 0; the weight inequality of the proof and its sharpness; the estimate error 1/64 for the tolerance r/256; and (30) for every refinement of Algorithm 1, as a statement about one refinement with arbitrary replies within (h/4)/256 and ties to the left.

Not covered: Convexity of the spectral function F, Lemma 2.1, which enters as a premise. The measure representation used in the paper's proof is not formalized; Lean proves (29) from three-point convexity inequalities.

Lean fields:

- `KE02.BasicSelectorCertificate.weights`, proved by `KE02.weights_le`: For h > 0, w\_(t-h/4,h/4) + w\_(t+h/4,h/4) ≤ (4/3) w\_(t,h) pointwise.
- `KE02.BasicSelectorCertificate.weights_attained`, proved by `KE02.weights_attained`: Equality at x = t - h/4, so 4/3 cannot be lowered.
- `KE02.BasicSelectorCertificate.children_sum`, proved by `KE02.basic_children_sum`: For convex F and h > 0: S\_(h/4)(t - h/4) + S\_(h/4)(t + h/4) ≤ (4/3) S\_h(t).
- `KE02.BasicSelectorCertificate.contraction`, proved by `KE02.basic_contraction`: (29) for convex F and h > 0.
- `KE02.BasicSelectorCertificate.estimate_error`, proved by `KE02.basic_estimate_error`: Three values within r/256 give the centred estimate within 1/64.
- `KE02.BasicSelectorCertificate.step`, proved by `KE02.basic_step`: (30) for one refinement of Algorithm 1: five replies within (h/4)/256, the smaller computed child variation selected, ties to the left.

Exact checks:

- `verification/core/check_constants.py:fam_c09` (family C09)

**Theorem 4.1** (`thm:selection-basic`, page 15). Basic iteration bound and certified scale. Coverage: formalized scalar part only.

Covered: S\_h(t) < n^3 from (9); K\_b least and equal to ⌈log\_(3/2)(16n^3)⌉; (2/3)^(K\_b) n^3 ≤ 1/16; for every real sequence obeying (30) with s\_0 < n^3, the iterated bound, the geometric sum below 3/32 and s\_(K\_b) < 5/32; 5/32 + 2/64 < 1/2; the arithmetic fact 3 + 5j ≤ 3 + 5K\_b; and (δ/(2n)) 4^-j ≤ δ/(2n) < 1.

Not covered: The run of Algorithm 1: termination, (31), the evaluation count, and the gap bound, which uses Proposition 3.1 and ‖tX‖\_2 = nt.

Lean fields:

- `KE02.BasicSelectorCertificate.initial`, proved by `KE02.basic_initial`: From (9): S\_h(t) < n^3 for n ≥ 1 and h > 0.
- `KE02.BasicSelectorCertificate.Kb_spec`, proved by `KE02.basicK_spec`: K\_b is the least natural number with (3/2)^(K\_b) ≥ 16n^3.
- `KE02.BasicSelectorCertificate.Kb_ceil`, proved by `KE02.basicK_ceil`: K\_b = ⌈log\_(3/2)(16n^3)⌉ for n ≥ 1.
- `KE02.BasicSelectorCertificate.first_term`, proved by `KE02.first_term`: (2/3)^(K\_b) n^3 ≤ 1/16.
- `KE02.BasicSelectorCertificate.iterate`, proved by `KE02.basic_iterate`: For every real sequence with s\_0 < n^3 and s\_(j+1) ≤ (2/3)s\_j + 1/32: s\_j < (2/3)^j n^3 + (1/32) Σ\_(l<j) (2/3)^l.
- `KE02.BasicSelectorCertificate.geometric`, proved by `KE02.geometric`: (1/32) Σ\_(l<j) (2/3)^l < 3/32.
- `KE02.BasicSelectorCertificate.final`, proved by `KE02.basic_final`: For such a sequence, s\_(K\_b) < 5/32.
- `KE02.BasicSelectorCertificate.stopping_constants`, proved by `KE02.basicSelectorCertificate`: 5/32 + 2/64 < 1/2.
- `KE02.BasicSelectorCertificate.calls`, proved by `KE02.basicSelectorCertificate`: The arithmetic fact 3 + 5j ≤ 3 + 5K\_b for j ≤ K\_b; the evaluation count of Algorithm 1 is not formalized.
- `KE02.BasicSelectorCertificate.radius_lt_one`, proved by `KE02.basic_radius_lt_one`: (δ/(2n)) 4^-j ≤ δ/(2n) < 1 for δ < 1/2.

Exact checks:

- `verification/core/check_constants.py:fam_c10` (family C10)
- `verification/core/check_constants.py:fam_c13` (family C13)

**Remark 4.1** (`rem:basic-selection-scale`, page 16). A lower bound on the window radius. Coverage: formalized scalar part only.

Covered: (32) for every radius (δ/(2n)) 4^-j with j ≤ K\_b, n ≥ 1, δ > 0 and α = log\_(3/2) 4.

Not covered: That the returned radius has this form, which comes from the run of Algorithm 1 (Theorem 4.1).

Lean fields:

- `KE02.BasicSelectorCertificate.radius`, proved by `KE02.basic_radius`: (32) for every radius (δ/(2n)) 4^-j with j ≤ K\_b, n ≥ 1, δ > 0 and α = log\_(3/2) 4.

Exact checks:

- `verification/core/check_constants.py:fam_c10` (family C10)

**Algorithm 2** (`alg:selection`, page 17). Improved selection of a separating perturbation. Coverage: formalized in full.

Covered: Algorithm 2 is the Lean transcript KE02.alg2Run for an arbitrary reply function, line by line: K least with 2^K ≥ 16n^3 and found by doubling, θ = 1/(4K), the three initial requests and the seven plus one requests of each refinement with their tolerances, the selection with ties to the left and the stopping test. Under the accuracy premise and for convex F with (9), the run executes a return statement at the first successful test, so the last line is not reached, after exactly 3 + 8j requests for j refinements.

Not covered: Convexity of the spectral function and (9), from Lemma 2.1, are premises; that the replies come from the oracle of Lemma 4.3 is not formalized.

Lean fields:

- `KE02.Algorithm2Certificate.K_spec`, proved by `KE02.alg2K_spec`: K is the least natural number with 16n^3 ≤ 2^K.
- `KE02.Algorithm2Certificate.K_doubling`, proved by `KE02.alg2K_doubling`: Repeated doubling from 1 returns K.
- `KE02.Algorithm2Certificate.theta_range`, proved by `KE02.alg2Theta_facts`: θ = 1/(4K) satisfies 0 < θ ≤ 1/4 and 1/2 - θ = (1 - 1/(2K))/2.
- `KE02.EndpointCertificate.child_windows`, proved by `KE02.child_windows`: Ring identities: the candidate windows of radius h' = (1/2 - θ)h centred at t ∓ h' are [t - (1-2θ)h, t] and [t, t + (1-2θ)h].
- `KE02.EndpointCertificate.points_of_children`, proved by `KE02.points_of_children`: The two child endpoint variations are the endpoint estimates formed from the values of F at the seven points (points 0-3 and 3-6).
- `KE02.EndpointCertificate.ties_left`, proved by `KE02.selectCenter_tie`: The selection rule moves to t - h when the two computed estimates are equal.
- `KE02.Algorithm2Certificate.run`, proved by `KE02.algorithm2_outcome`: For every n ≥ 1, δ > 0, convex F satisfying (9) and every reply function whose replies to the requests of the run are within the requested errors, the run of Algorithm 2 satisfies every field of KE02.Algorithm2Outcome.
- `KE02.Algorithm2Outcome.returns`, proved by `KE02.algorithm2_outcome`: The run executes a return statement.
- `KE02.Algorithm2Outcome.state_eq`, proved by `KE02.algorithm2_outcome`: The returned state is the state reached after the performed refinements.
- `KE02.Algorithm2Outcome.earlier_tests_fail`, proved by `KE02.algorithm2_outcome`: Every earlier stopping test fails.
- `KE02.Algorithm2Outcome.returned_test_passes`, proved by `KE02.algorithm2_outcome`: The returned state passes the stopping test Ŝ\_h(t) + 1/64 < 1/2.
- `KE02.Algorithm2Outcome.calls_exact`, proved by `KE02.algorithm2_outcome`: The request log has exactly 3 + 8j entries after j refinements.

Exact checks:

- `verification/core/check_constants.py:fam_c12` (family C12)
- `verification/core/check_constants.py:fam_c13` (family C13)

Numerical illustration, not part of any proof: items `adaptive` and `fallback` in Section 5 below.

**Lemma 4.2** (`lem:potential-contraction`, `lem:potential-inexact`, page 17). Contraction of endpoint slope variation. Coverage: formalized in full.

Covered: (35) for every convex F, 0 < θ ≤ 1/4 and h > 0, with the sum inequality of the proof; the estimate error 1/64 for the tolerance 2θh'/256; and (36), for one refinement with arbitrary replies and at every performed refinement of every run of Algorithm 2 whose replies meet the requested accuracies.

Not covered: Convexity of the spectral function F, Lemma 2.1, which enters as a premise.

Lean fields:

- `KE02.EndpointCertificate.children_sum`, proved by `KE02.endpoint_children_sum`: For convex F, 0 < θ ≤ 1/4 and h > 0, the two child endpoint variations sum to at most the parent one (proof of Lemma 4.2).
- `KE02.EndpointCertificate.contraction`, proved by `KE02.endpoint_contraction`: (35) for convex F, 0 < θ ≤ 1/4 and h > 0.
- `KE02.EndpointCertificate.estimate_error`, proved by `KE02.endpoint_estimate_error`: Four values within 2θh/256 give an endpoint estimate within 1/64 of S\_h^(θ).
- `KE02.EndpointCertificate.potential_step`, proved by `KE02.endpoint_potential_step`: (36) for one refinement: with the seven replies within 2θh'/256, the selected centre satisfies S\_h'^(θ) ≤ S\_h^(θ)(t)/2 + 1/32.
- `KE02.Algorithm2Outcome.potential_step`, proved by `KE02.algorithm2_outcome`: (36) at every performed refinement.

Exact checks:

- `verification/core/check_constants.py:fam_c11` (family C11)

**Theorem 4.2** (`thm:selection`, page 18). Improved constructive spectral separation. Coverage: formalized scalar part only.

Covered: For every n ≥ 1, δ > 0, convex F with (9) and every reply function that meets the requested accuracies: termination after at most K = ⌈log\_2(16n^3)⌉ refinements; (37), that is S\_h(t) < 1/2, [t - h, t + h] ⊆ [0, δ/n] and h > δ/(128n^4); at most 3 + 8K evaluations, all at points of [0, δ/n]; nested windows and the potential bounds of the proof; the stopping-test error θ/32 ≤ 1/128 and 1/8 + 1/128 + 1/64 < 1/2; Bernoulli's inequality and L\_K > δ/(64n^4); h ≤ δ/(2n) < 1, 0 ≤ t and nt ≤ δ; and the scalar inequality h^2/(2^20 n^4) > 2^-34 δ^2 n^-12 used for (38). The premises are satisfiable.

Not covered: (38) itself, which applies Proposition 3.1, and ‖D‖\_2 = nt; that F is the spectral function, whose convexity and secant bounds (9) are Lemma 2.1.

Lean fields:

- `KE02.Algorithm2Certificate.K_ceil_log`, proved by `KE02.alg2K_ceil`: K = ⌈log\_2(16n^3)⌉ for n ≥ 1.
- `KE02.Algorithm2Certificate.K_upper`, proved by `KE02.alg2K_pos`, `KE02.alg2K_upper`: 2^K < 32n^3 and K ≥ 1 for n ≥ 1.
- `KE02.Algorithm2Certificate.bernoulli`, proved by `KE02.bernoulli_half`: (1 - 1/(2K))^K ≥ 1/2 for K ≥ 1.
- `KE02.Algorithm2Certificate.LK_bound`, proved by `KE02.LK_bound`: L\_K = (δ/n)(1/2 - θ)^K > δ/(64n^4) for n ≥ 1 and δ > 0.
- `KE02.Algorithm2Certificate.stopping_constants`, proved by `KE02.algorithm2Certificate`: 1/8 + 1/128 + 1/64 < 1/2.
- `KE02.Algorithm2Certificate.midpoint_estimate_error`, proved by `KE02.midpoint_estimate_error`: For 0 < θ ≤ 1/4, three values within 2θh/256 give the centred estimate within θ/32 ≤ 1/128.
- `KE02.Algorithm2Certificate.run`, proved by `KE02.algorithm2_outcome`: For every n ≥ 1, δ > 0, convex F satisfying (9) and every reply function whose replies to the requests of the run are within the requested errors, the run of Algorithm 2 satisfies every field of KE02.Algorithm2Outcome.
- `KE02.Algorithm2Certificate.premises_satisfiable`, proved by `KE02.algorithm2_premises_satisfiable`: For every n ≥ 1 and δ > 0 some F and reply function satisfy all premises of run.
- `KE02.Algorithm2Outcome.refinements_le`, proved by `KE02.algorithm2_outcome`: It performs at most K refinements.
- `KE02.Algorithm2Outcome.radius_formula`, proved by `KE02.algorithm2_outcome`: h\_j = (1/2 - θ)^j δ/(2n) for every j.
- `KE02.Algorithm2Outcome.windows_inside`, proved by `KE02.algorithm2_outcome`: Every window [t\_j - h\_j, t\_j + h\_j] lies in [0, δ/n].
- `KE02.Algorithm2Outcome.windows_nested`, proved by `KE02.algorithm2_outcome`: Every window lies in the previous one.
- `KE02.Algorithm2Outcome.initial_potential`, proved by `KE02.algorithm2_outcome`: The initial endpoint variation is below n^3, from (9).
- `KE02.Algorithm2Outcome.potential_bound`, proved by `KE02.algorithm2_outcome`: The iterated form of (36) used in the proof of Theorem 4.2.
- `KE02.Algorithm2Outcome.potential_final`, proved by `KE02.algorithm2_outcome`: If K refinements are performed, the endpoint variation is below 1/8.
- `KE02.Algorithm2Outcome.estimate_accuracy`, proved by `KE02.algorithm2_outcome`: The estimate of the returned test is within 1/64 of S\_h(t).
- `KE02.Algorithm2Outcome.centered_lt_half`, proved by `KE02.algorithm2_outcome`: (37), first part: S\_h(t) < 1/2 at the returned pair.
- `KE02.Algorithm2Outcome.radius_lower`, proved by `KE02.algorithm2_outcome`: (37), last part: h > δ/(128n^4).
- `KE02.Algorithm2Outcome.radius_upper`, proved by `KE02.algorithm2_outcome`: h ≤ δ/(2n).
- `KE02.Algorithm2Outcome.window`, proved by `KE02.algorithm2_outcome`: (37), middle part: [t - h, t + h] ⊆ [0, δ/n].
- `KE02.Algorithm2Outcome.budget`, proved by `KE02.algorithm2_outcome`: 0 ≤ t and nt ≤ δ, the scalar part of ‖D‖\_2 ≤ δ.
- `KE02.Algorithm2Outcome.queries_inside`, proved by `KE02.algorithm2_outcome`: Every request lies in [0, δ/n] and has a positive tolerance.
- `KE02.Algorithm2Outcome.calls_le`, proved by `KE02.algorithm2_outcome`: At most 3 + 8K requests.
- `KE02.Algorithm2Outcome.radius_lt_one`, proved by `KE02.algorithm2_outcome`: For δ < 1/2, h < 1, as Proposition 3.1 requires.
- `KE02.Algorithm2Outcome.gap_scale`, proved by `KE02.algorithm2_outcome`: h^2/(2^20 n^4) > 2^-34 δ^2 n^-12 at the returned radius: the scalar step of (38).
- `KE02.EndpointCertificate.points_in_parent`, proved by `KE02.refinePoint_in_parent`: For 0 < θ ≤ 1/4 and h > 0, the seven requested points of a refinement lie in the parent window [t - h, t + h].
- `KE02.LocalConstantsCertificate.gap_chain`, proved by `KE02.gap_chain`: h > δ/(128n^4) gives h^2/(2^20 n^4) > 2^-34 δ^2 n^-12.

Exact checks:

- `verification/core/check_constants.py:fam_c12` (family C12)
- `verification/core/check_constants.py:fam_c13` (family C13)

Numerical illustration, not part of any proof: items `adaptive` and `baselines` in Section 5 below.

**Remark 4.2** (`rem:selection-scale`, page 19). Improvement over the basic selector. Coverage: written proof only.

Covered: No Lean declaration or exact check is assigned; the quantities it compares are those of Lemma 4.2 and Theorems 4.1 and 4.2.

Not covered: The comparison of the two selectors.

**Lemma 4.3** (`lem:oracle`, page 19). Spectral-function oracle. Coverage: formalized scalar part only.

Covered: The algebra and arithmetic of Appendix A that the oracle uses: the recurrence ends in det(zI + 2I + A); k Graeffe steps give ∏(z + r\_j^(2^k)); p\_j ≤ e\_j ≤ 2^n p\_j; k least with 2^k η ≥ 8n and found by doubling, with 4n/R ≤ η/2; and, for roots in (0, 4), the index-wise matching with error η/2 in every eigenvalue and weighted error at most ε. The bound n(n+1)η/2 in the remark after the lemma is also formalized.

Not covered: The lemma as a statement about an algorithm: that the procedure applied to F(t) = Σ\_j jλ\_j(T + tX) meets the accuracy ε, P(z) = ∏(z + r\_j) (spectral theorem), the complex Hermitian c\_i, balanced product trees, Fourier transforms and roots of unity, the arithmetic model and the cost O(n[1 + log(n/ε)]^2).

Lean fields:

- `KE02.ContinuantCertificate.det_char`, proved by `KE02.det_char`: For every real A vanishing more than one step off the diagonal, det(zI + 2I + A) equals P\_n of the recurrence of Appendix A.
- `KE02.GraeffeCertificate.iterate`, proved by `KE02.graeffeIterate_rootPolynomial`: k Graeffe steps map ∏(X + r\_i) to ∏(X + r\_i^(2^k)).
- `KE02.CoefficientCertificate.bounds`, proved by `KE02.elementaryCoeff_bounds`: p\_j ≤ e\_j ≤ C(n,j) p\_j ≤ 2^n p\_j for positive nonincreasing roots and j ≤ n.
- `KE02.RootExtractionCertificate.steps_least`, proved by `KE02.graeffeSteps_least`: For η > 0, k is the least integer with 2^k η ≥ 8n.
- `KE02.RootExtractionCertificate.steps_doubling`, proved by `KE02.graeffeDoubling_spec`: Doubling R from 1 and comparing Rη with 8n returns k.
- `KE02.RootExtractionCertificate.steps_choice`, proved by `KE02.graeffeSteps_spec`: For n ≥ 1 and 0 < η < 1: 8n/η ≤ R < 16n/η, n ≤ R and 4n/R ≤ η/2.
- `KE02.RootExtractionCertificate.weighted_error`, proved by `KE02.weighted_error`: Errors ε/(2Σj) in every λ\_j give error at most ε in Σ\_j jλ\_j.
- `KE02.RootExtractionCertificate.pipeline`, proved by `KE02.pipeline`: For n ≥ 1, roots in (0, 4) in nonincreasing order and 0 < ε < 1, with η = ε/Σj and k found by doubling: λ\_j = r\_(n+1-j) - 2 is nondecreasing, every λ̂\_j = r̂\_(n+1-j) - 2 is within η/2 of λ\_j, and the weighted sum is within (n(n+1)/2)(η/2) ≤ ε.
- `KE02.RootExtractionCertificate.sum_error`, proved by `KE02.sum_error`: Errors η in every λ\_j give error at most n(n+1)η/2: the remark after Lemma 4.3.

Exact checks:

- `verification/core/check_constants.py:fam_c14` (family C14)
- `verification/core/check_appendix_a.py:fam_a04` (family A04)

**Equation (33)** (`eq:endpoint-slope`, page 16). Endpoint slope variation.

Covered: (33) is the Lean definition KE02.endpointVariation; it is nonnegative for convex F, 0 < θ ≤ 1/2 and h > 0.

Not covered: Convexity of the spectral function F, Lemma 2.1, which enters as a premise.

Lean fields:

- `KE02.EndpointCertificate.endpoint_nonneg`, proved by `KE02.endpoint_nonneg`: For convex F, 0 < θ ≤ 1/2 and h > 0: the endpoint slope variation (33) is nonnegative.

Exact checks:

- `verification/core/check_constants.py:fam_c11` (family C11)

**Equation (34)** (`eq:potential-controls-S`, page 17). Endpoint slopes control the centered slope variation.

Covered: (34) for convex F, 0 < θ ≤ 1/2 and h > 0.

Not covered: Convexity of the spectral function F, Lemma 2.1, which enters as a premise.

Lean fields:

- `KE02.EndpointCertificate.centered_le_endpoint`, proved by `KE02.centered_le_endpoint`: (34): S\_h(t) ≤ S\_h^(θ)(t) for convex F, 0 < θ ≤ 1/2 and h > 0.

Exact checks:

- `verification/core/check_constants.py:fam_c11` (family C11)

**Equation (40)** (`eq:minimum-oracle-accuracy`, page 20). The smallest requested accuracy.

Covered: Every request of a run has an accuracy above δ/(2^16 K n^4) and at most δ/(512n).

Not covered: The consequence log(n/ε\_min) = O(1 + log(n/δ)) and the total cost.

Lean fields:

- `KE02.Algorithm2Outcome.min_accuracy`, proved by `KE02.algorithm2_outcome`: (40): every requested accuracy exceeds δ/(2^16 K n^4).
- `KE02.Algorithm2Outcome.tolerance_upper`, proved by `KE02.algorithm2_outcome`: Every requested accuracy is at most δ/(512n).

Exact checks:

- `verification/core/check_constants.py:fam_c12` (family C12)

## 5. Numerical illustrations

Section 5 contains no numbered result. Its tables and figures are produced from the code and data in [verification/numerics/](../verification/numerics/README.md), which need numpy, scipy, pandas, matplotlib and python-flint and are not run by the exact checks. They illustrate the algorithm and are not used in any proof. The selection path is computed in double precision without certified comparisons; rigorous Sturm enclosures certify the stopping test along it and the direct gaps. File paths below are relative to `verification/numerics/`.

- `families` (`tab:test-families`): `ke02num/core.py`. make\_matrix generates the six test families of Table 1.
- `adaptive` (`tab:certified-results`, `fig:certified-iterations`, `fig:certified-gaps`, `fig:certified-runtime`): `run_adaptive.py`, `ke02num/hybrid.py`, `data/adaptive.jsonl`. The certified pipeline of Section 5: a double-precision selection path, rigorous Sturm enclosures of the centred slope variation along it, the first certified stop j\_\*, the certificates g\_S and g\_dir and the run times (Table 2, Figures 4 to 6). The selection path is not certified.
- `baselines` (`fig:certified-baselines`): `run_sweep.py`, `run_direct_s.py`, `data/sweep.jsonl`, `data/directS_fp.jsonl`. The double-precision baseline sweep and direct centred tests behind the distributions of Figure 7; its stars use the certified pipeline of the item adaptive. Numerical comparisons, not gap certificates.
- `fallback` (no table or figure): `run_fallback.py`. Runs all K refinements of Algorithm 2 with rigorously decided endpoint comparisons and prints a summary; Section 5 states that its runs are not reported.

## 6. Conclusions and outlook

Section 6 contains no numbered result and no claim beyond those mapped above; it lists the open directions.

## Appendix A. The spectral-function oracle: algebraic details

Appendix A contains no numbered result. Its algebra is formalized in four components of the certificate, `graeffe`, `coefficients`, `rootExtraction` and `continuant`, and checked exactly by the families A01 to A04 and C14.

**Appendix A** (`app:oracle`, page 27). The spectral-function oracle: algebraic details.

Covered: The determinant of a tridiagonal matrix over any commutative ring R : Type is the continuant, and for every real tridiagonal A the recurrence ends in det(zI + 2I + A), with c\_i = A\_(i,i+1)^2 for symmetric A; the even/odd split, one Graeffe step and its k-th iterate ∏(z + r\_j^(2^k)) for all real roots; the e\_j as elementary symmetric sums, positive, with p\_j ≤ e\_j ≤ C(n,j) p\_j ≤ 2^n p\_j; the R-th root as k square roots; 2^x - 1 ≤ x on [0, 1]; |r̂\_j - r\_j| ≤ 4n/R; k least with Rη ≥ 8n and found by doubling R from 1, so that 8n/η ≤ R < 16n/η and 4n/R ≤ η/2; η = ε/Σj and the index-wise matching λ̂\_j = r̂\_(n+1-j) - 2 with weighted error at most ε.

Not covered: P(z) = ∏(z + r\_j) and r\_j ∈ (0, 4), which need the spectral theorem and are premises in Lean; the complex Hermitian c\_i = (Re A\_(i,i+1))^2 + (Im A\_(i,i+1))^2, checked exactly on instances only; balanced product trees, Fourier transforms and roots of unity; the operation counts; and the coefficient growth e\_j ≤ 2^n 4^(nR).

Lean fields:

- `KE02.ContinuantCertificate.det_tridiag`, proved by `KE02.det_tridiag`: The determinant of a k x k tridiagonal matrix over any commutative ring R : Type is the continuant.
- `KE02.ContinuantCertificate.det_char`, proved by `KE02.det_char`: For every real A vanishing more than one step off the diagonal, det(zI + 2I + A) equals P\_n of the recurrence of Appendix A.
- `KE02.ContinuantCertificate.symmetric_coeff`, proved by `KE02.symmetric_coeff`: For symmetric A, c\_i = A\_(i,i+1)^2.
- `KE02.GraeffeCertificate.even_coeff`, proved by `KE02.evenPart_coeff`: The coefficients of the even part E are those of P at even indices.
- `KE02.GraeffeCertificate.odd_coeff`, proved by `KE02.oddPart_coeff`: The coefficients of the odd part O are those of P at odd indices.
- `KE02.GraeffeCertificate.reconstruct`, proved by `KE02.graeffe_reconstruct`: P(z) = E(z^2) + zO(z^2) for every real polynomial.
- `KE02.GraeffeCertificate.one_step`, proved by `KE02.graeffe_rootPolynomial`: One Graeffe step maps ∏(X + r\_i) to ∏(X + r\_i^2), for all real roots.
- `KE02.GraeffeCertificate.iterate`, proved by `KE02.graeffeIterate_rootPolynomial`: k Graeffe steps map ∏(X + r\_i) to ∏(X + r\_i^(2^k)).
- `KE02.CoefficientCertificate.expansion`, proved by `KE02.elementaryCoeff_expansion`: The coefficient e\_j of ∏(X + r\_i^(2^k)) is the elementary symmetric sum of degree j.
- `KE02.CoefficientCertificate.leading`, proved by `KE02.elementaryCoeff_zero`: e\_0 = 1.
- `KE02.CoefficientCertificate.positive`, proved by `KE02.elementaryCoeff_pos`: e\_j > 0 for positive roots and j ≤ n.
- `KE02.CoefficientCertificate.bounds`, proved by `KE02.elementaryCoeff_bounds`: p\_j ≤ e\_j ≤ C(n,j) p\_j ≤ 2^n p\_j for positive nonincreasing roots and j ≤ n.
- `KE02.RootExtractionCertificate.graeffe_coeff`, proved by `KE02.graeffeCoeff_eq`: The coefficients of the actual k-th Graeffe iterate are the e\_j.
- `KE02.RootExtractionCertificate.coeff_bounds`, proved by `KE02.graeffeCoeff_bounds`: p\_j ≤ e\_j ≤ 2^n p\_j for the actual iterate.
- `KE02.RootExtractionCertificate.iterated_sqrt`, proved by `KE02.iteratedSqrt_eq`: x^(1/2^k) is k successive square roots for x ≥ 0.
- `KE02.RootExtractionCertificate.two_rpow_sub_one_le`, proved by `KE02.two_rpow_sub_one_le`: 2^x - 1 ≤ x for 0 ≤ x ≤ 1.
- `KE02.RootExtractionCertificate.root_error`, proved by `KE02.root_error`: |r̂\_j - r\_j| ≤ 4n/R when 0 < r\_j < 4 and n ≤ R.
- `KE02.RootExtractionCertificate.steps_least`, proved by `KE02.graeffeSteps_least`: For η > 0, k is the least integer with 2^k η ≥ 8n.
- `KE02.RootExtractionCertificate.steps_doubling`, proved by `KE02.graeffeDoubling_spec`: Doubling R from 1 and comparing Rη with 8n returns k.
- `KE02.RootExtractionCertificate.steps_choice`, proved by `KE02.graeffeSteps_spec`: For n ≥ 1 and 0 < η < 1: 8n/η ≤ R < 16n/η, n ≤ R and 4n/R ≤ η/2.
- `KE02.RootExtractionCertificate.weighted_error`, proved by `KE02.weighted_error`: Errors ε/(2Σj) in every λ\_j give error at most ε in Σ\_j jλ\_j.
- `KE02.RootExtractionCertificate.pipeline`, proved by `KE02.pipeline`: For n ≥ 1, roots in (0, 4) in nonincreasing order and 0 < ε < 1, with η = ε/Σj and k found by doubling: λ\_j = r\_(n+1-j) - 2 is nondecreasing, every λ̂\_j = r̂\_(n+1-j) - 2 is within η/2 of λ\_j, and the weighted sum is within (n(n+1)/2)(η/2) ≤ ε.

Exact checks:

- `verification/core/check_appendix_a.py:fam_a01` (family A01)
- `verification/core/check_appendix_a.py:fam_a02` (family A02)
- `verification/core/check_appendix_a.py:fam_a04` (family A04)
- `verification/core/check_constants.py:fam_c14` (family C14)

**Equation (43)** (`eq:graeffe`, page 27). The Graeffe ratio bound.

Covered: (43) for positive nonincreasing roots and R = 2^k, in ratio form and with real R-th roots.

Not covered: That the roots are r\_j = 2 + λ\_(n+1-j)(A), which needs the spectral theorem.

Lean fields:

- `KE02.CoefficientCertificate.ratio_bounds`, proved by `KE02.elementaryCoeff_ratio_bounds`: r\_i^R/2^n ≤ e\_(i+1)/e\_i ≤ 2^n r\_i^R with R = 2^k (Lean index i is the paper's j = i + 1).
- `KE02.RootExtractionCertificate.ratio_root`, proved by `KE02.ratio_root`: (43) with R = 2^k and real powers.

Exact checks:

- `verification/core/check_appendix_a.py:fam_a03` (family A03)

## Exact-check families

The families are functions of the two checkers in [verification/core/](../verification/core/README.md); [CHECKERS.txt](../verification/core/CHECKERS.txt) lists their negative controls.

- C01, `verification/core/check_constants.py:fam_c01`: Σj = n(n+1)/2 and Σjn = n^2(n+1)/2; the slope width (n^3 - n)/2 < n^3 for n ≤ 10^4; the identities (8) and (10) on exact sorted spectra with n ≤ 9; and (9), midpoint convexity and 0 ≤ S\_h(t) ≤ (n^3 - n)/2 on 400 exact diagonal instances with n ≤ 8. Limitation: Finite ranges and diagonal instances; Lemma 2.1 for every Hermitian T is proved in the paper.
- C02, `verification/core/check_constants.py:fam_c02`: (16) and (17) on a grid; Example 4.1 exactly; the crossing points 0.06, 0.08, 0.10 and an exact bracket of S\_0.006(0.08) that rounds to 1.8541 (Example 2.3); for Example 3.1, ‖H‖\_2 < 1, nonzero couplings, the two eigenvalues to 10^-12 and |λ - μ| < γ; for Example 3.2, τ ≈ 0.0358 and the column L\_k ≤ τ for the printed values L\_k. Limitation: Only the listed claims; the printed eigenvectors, residuals and leakages of Examples 3.1 and 3.2 are not recomputed.
- C03, `verification/core/check_constants.py:fam_c03`: n(1/(2√n))^2 = 1/4, 3/4, (3/4)/2 = 3/8 and √(3/8) > 1/2; the projector-gap identity; the whole of Step 1 on exact n x 2 matrices with orthonormal rational columns. Limitation: Fixed exact instances; Step 1 for all matrices is proved in the paper.
- C04, `verification/core/check_constants.py:fam_c04`: The discrete Wronskian identity (22) in telescoping form for arbitrary vectors and for exact eigenpairs; the bound 1/2 for orthonormal rational pairs. Limitation: Fixed exact instances; the identity and the bound for all real sequences are Lean theorems.
- C05, `verification/core/check_constants.py:fam_c05`: τ^2 = 16nγ, τ ≤ 1/(4√n), cases (a) and (c) including the determinant step from the three-term recurrence, 5γ/τ^2 = 5/(16n) and (n - 1)·5/(16n) < 5/16 < 1/2 for n ≤ 10^4. Limitation: Finite range of n and fixed instances; the existence of the cut is proved in the paper.
- C06, `verification/core/check_constants.py:fam_c06`: The residual of w\_1, the commutator [H, P\_L]w and its bound √2 τ, 2√n(γ/2 + √2 τ) ≤ 16n√γ, and the X-responses at most k and at least k + 1. Limitation: Fixed exact instances; the matrix estimates of Step 4 are proved in the paper.
- C07, `verification/core/check_constants.py:fam_c07`: H - H̃ = AQ + QA - QAQ, H̃v\_i = ((λ+μ)/2)v\_i, ‖AQ‖\_F^2 = Σ\_i ‖Av\_i‖^2, rank at most two and ‖M‖\_\* ≤ √2 ‖M‖\_F on exact instances; 3√2·√2·16 = 96; (27) for an exact diagonal H̃ with a repeated eigenvalue. Limitation: Fixed exact instances; the matrix statements of Lemma 3.2 are proved in the paper.
- C08, `verification/core/check_constants.py:fam_c08`: 0 < h ≤ 1 gives γ ≤ 1/(256n^2); the transfer coefficient 1 + 2 + 1 = 4; (4n/h)·96n√γ = 384/1024 = 3/8 and 5/8 > 1/2, symbolically, for n ≤ 10^4 at h = 1 and on 2000 sampled chains; (28) on exact diagonal pairs. Limitation: Finite ranges and instances; the matrix statements are proved in the paper.
- C09, `verification/core/check_constants.py:fam_c09`: The weight inequality of the proof of Lemma 4.1 with its extremal value 4/3, completely (both sides are piecewise linear in (x - t)/h and every breakpoint is checked); the representation of S\_h(t) as an integral of the weights, (29), its sharpness, and (30) with replies within r/256, on random convex piecewise-linear F. Limitation: Random convex piecewise-linear functions; (29) and (30) for every convex F are proved in Lean and in the paper.
- C10, `verification/core/check_constants.py:fam_c10`: K\_b least with (3/2)^(K\_b) ≥ 16n^3 by two methods, (2/3)^(K\_b) n^3 ≤ 1/16 and s\_(K\_b) < 5/32 for n ≤ 10^4; the closed form of the iteration; 5/32 + 2/64 < 1/2; (31); (32) reduced to (3/2)^(K\_b - 1) < 16n^3; five evaluations per refinement. Limitation: Finite range of n.
- C11, `verification/core/check_constants.py:fam_c11`: (34) for 0 < θ ≤ 1/2; (35) and the three secant orderings of its proof for 0 < θ ≤ 1/4; sharpness of 1/2; the error 1/64 from the tolerance 2θh'/256; and (36), on random convex piecewise-linear F. Limitation: Random convex piecewise-linear functions; the statements for every convex F are proved in Lean and in the paper.
- C12, `verification/core/check_constants.py:fam_c12`: For 2 ≤ n ≤ 10^4: K by doubling equals the least K with 2^K ≥ 16n^3 and ⌈log\_2(16n^3)⌉, 2^K < 32n^3, θ = 1/(4K) ≤ 1/28, the potential bound below 1/8, θ/32 ≤ 1/128, 1/8 + 1/128 + 1/64 < 1/2, (1/2 - θ)^K > 1/(64n^3), h > δ/(128n^4), (40) and eight evaluations per refinement; Bernoulli's bound for K ≤ 1024; the reduction of h^2/(2^20 n^4) > 2^-34 δ^2 n^-12 (128^2·2^20 = 2^34) and sampled instances; and (5). Limitation: Finite ranges of n and K.
- C13, `verification/core/check_constants.py:fam_c13`: Algorithms 1 and 2 run as transcripts on exact instances (diagonal T, whose gap is computed exactly, and convex piecewise-linear F satisfying (9), including kink trees that force up to 8 refinements), with exact replies and with replies within the tolerances: termination within K\_b and K refinements, 3 + 5j and 3 + 8j requests, nesting in [0, δ/n], (30) and (36) along the run, (31) and (37), (40), and gap(T + tX) > h^2/(2^20 n^4) > 2^-34 δ^2 n^-12 for diagonal T. Limitation: Fixed exact instances; diagonal T is the only case in which the gap is computed.
- C14, `verification/core/check_constants.py:fam_c14`: η = ε/Σj = 2ε/(n(n+1)), n/η ≤ (n/ε)^3, R = 2^k by doubling with 8n/η ≤ R < 16n/η, n ≤ R and 4n/R ≤ η/2; 2^x - 1 ≤ x and 1 - 2^-x ≤ x at every rational x = p/q in [0, 1] with q ≤ 40; rn/R < 4n/R for 0 < r < 4; total error Σ\_j jη/2 = ε/2 ≤ ε. Limitation: Finite ranges and rational sample points.
- A01, `verification/core/check_appendix_a.py:fam_a01`: The recurrence P\_0 = 1, P\_1 = z + 2 + a\_1, P\_i = (z + 2 + a\_i)P\_(i-1) - c\_(i-1)P\_(i-2) equals det(zI + 2I + A) as an exact polynomial, with the determinant computed independently by rational elimination and interpolation, and for n ≤ 7 also by the permutation expansion: 48 real symmetric instances (n ≤ 8), 32 complex Hermitian instances with c\_i = (Re A\_(i,i+1))^2 + (Im A\_(i,i+1))^2, and scaled Kac matrices. Limitation: Fixed exact instances; for every real tridiagonal matrix the identity is a Lean theorem, and the complex Hermitian case is proved in the paper.
- A02, `verification/core/check_appendix_a.py:fam_a02`: P(z) = E(z^2) + zO(z^2); G(P)(z) = E(-z)^2 + zO(-z)^2 = ∏(z + r\_j^2) and k steps give ∏(z + r\_j^(2^k)), monic, for random rational roots with mixed signs, zeros and ties; the coefficient of z^(n-j) is e\_j. Limitation: Random rational root lists; the identities for all real roots are proved in Lean.
- A03, `verification/core/check_appendix_a.py:fam_a03`: For r\_1 ≥ ... ≥ r\_n > 0 with ties and R = 2^k, k ≤ 6: e\_0 = 1, e\_j > 0, p\_j ≤ e\_j ≤ C(n,j) p\_j ≤ 2^n p\_j, and (43) in R-th-power form. Limitation: Fixed root lists and k ≤ 6; the bounds for all roots are proved in Lean.
- A04, `verification/core/check_appendix_a.py:fam_a04`: The complete pipeline: Gershgorin ‖A‖\_2 < 2, the integer-scaled recurrence, P(z) = ∏(z + r\_j) where the spectrum is known, η, R by doubling, k Graeffe steps, (e\_j/e\_(j-1))^(1/R) by k verified square roots, (43), |r̂\_j - r\_j| ≤ 4n/R, the index-wise matching with |λ̂\_j - λ\_j| ≤ η/2 and the weighted error at most ε, on scaled Clement matrices, Pythagorean 2 x 2 blocks, diagonal matrices with repeated eigenvalues and generic rational matrices with exact Sturm brackets; R up to 2^13. Limitation: Fixed instances; the oracle for every input and its cost are proved in the paper.
