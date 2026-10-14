# Results by paper section

The numbering follows the [paper](../paper/main.pdf). This file is generated from [mapping.json](mapping.json); the checker verifies the complete numbered-result inventory.

Each formal scope is stated separately. Exact computations check finite instances or explicit arithmetic identities; they do not establish a uniform matrix theorem or an asymptotic bound.


## 1. The main theorem and its context

| Result | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Theorem 1.1 — Deterministic diagonal spectral separation<br>`thm:main` | For every n >= 2, Hermitian tridiagonal T with operator norm <= 1, and real 0 < delta < 1/2, return D = t diag(1,...,n), 0 <= t <= delta/n, with norm(D) <= delta and gap(T+D) > 2^(-88)(delta/n)^42 in O(n[1+log(n/delta)]^3) exact real operations and comparisons. Nonnegative square roots have unit cost; no input bits are extracted. | **Paper only.** The uniform matrix gap and exact-operation bound are proved in the paper. The cited certificate proves only the scalar and polynomial ingredients. It does not include Hermitian spectral theory, quasimodes, the gap implication, the value oracle or runtime. No finite-bit or floating-point conclusion follows from this cost model.<br>[KE02.coreCertificate](../lean/KE02.lean): Aggregate of the scalar selector, Graeffe identities and coefficient inequalities, with precisely their stated hypotheses and exclusions. | [constants](#constants), [primitives](#primitives), [selector](#selector), [inverse](#inverse), [recursive](#recursive) |

## 2. A convex weighted spectral function

| Result | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Lemma 2.1 — Weighted spectral variational formula<br>`lem:variational` | For every Hermitian A, f(A) = sum(j lambda_j(A)) is max tr(GA) over the unitary orbit of diag(1,...,n). Its operator-norm Lipschitz constant is W=n(n+1)/2; F(t)=f(T+tX) is convex with secant slopes in [W,nW]. | **Paper only.** The spectral variational formula, Lipschitz inequality and matrix-specific convexity and slope bounds are not formalized. Lean takes scalar convexity and the initial potential bound as hypotheses.<br>No declaration cited. | Paper only. |
| Remark 2.2 — Reduction to real eigenvectors<br>`rem:gauge` | Diagonal unitary conjugation makes a Hermitian tridiagonal matrix real symmetric with nonnegative edges, separately on each connected component, and commutes with X and every real diagonal perturbation. The algorithm uses squared edge magnitudes without constructing the phases. | **Paper only.** The phase gauge and its spectral invariance are proved in the paper, including zero edges; there is no corresponding Lean declaration.<br>No declaration cited. | Paper only. |

## 3. Quasimodes with ordered disjoint supports

| Result | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Lemma 3.1 — Ordered disjoint-support quasimodes<br>`lem:quasimodes` | For real symmetric tridiagonal H of order n >= 2 and norm <= 2 with edges of magnitude <= 1, and orthonormal eigenvectors at eigenvalues differing by at most 0 < h <= 1/(256 n^6), put E=(lambda+mu)/2 and tau=(16 n^2 h)^(1/4). There are ordered disjoint-support unit vectors a,b with full-matrix residuals <= 2 n tau and b^T X b - a^T X a >= 1. | **Paper only.** The existence argument and its uniform quantifiers are paper proofs. Exact rational eigenpair and boundary fixtures check supporting identities and constants, not this all-matrix assertion.<br>No declaration cited. | [inverse](#inverse), [constants](#constants) |

## 4. Small gaps force a convexity defect

| Result | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Lemma 4.1 — Small gaps force a convexity defect<br>`lem:defect` | If H is real symmetric tridiagonal of order n >= 2 and norm <= 2, its edge magnitudes are <= 1, 0 < r <= 1, and gap(H) <= h_r = r^4/(10^12 n^14), then f(H+rX)+f(H-rX)-2f(H) >= r/2. | **Paper only.** The quasimode-to-defect implication, Hermitian flattening and weight-swap argument are proved in the paper. Rational examples and constant arithmetic supply finite supporting checks.<br>No declaration cited. | [inverse](#inverse), [constants](#constants) |
| Remark 4.2 — Repeated eigenvalues and the nearby matrix<br>`rem:repeated` | The small-gap proof includes gap(H)=0 by using the positive h_r and never dividing by the actual gap. The auxiliary Hermitian matrix H prime need not be tridiagonal. | **Paper only.** The degenerate spectral case and use of the auxiliary matrix are paper statements. Formal polynomial identities separately allow repeated roots, without proving this spectral remark.<br>No declaration cited. | [inverse](#inverse) |

## 5. A robust two-child interval rule

| Result | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Lemma 5.1 — Child potentials and centered defect<br>`lem:children` | For a convex real function on [a,b] of positive length L, the middle-quarter children have potential sum at most the parent potential. At c=(a+b)/2 and r=L/4, the centered second difference is at most r times the parent potential. | **Formal scalar result.** Both inequalities hold formally for every convex real function and every positive-length subinterval in its domain. The defect inequality is written in multiplied form, equivalent because r > 0. No spectral hypothesis is part of these declarations.<br>[KE02.selector_children_sum](../lean/KE02/SelectorGeometry.lean): The sum of the two actual middle-quarter child potentials is at most the parent potential.<br>[KE02.selector_defect_le](../lean/KE02/SelectorGeometry.lean): The centered second difference is at most selectorRadius times selectorPotential. | [selector](#selector) |
| Lemma 5.2 — Selection from approximate values<br>`lem:robust-choice` | If the four replies on each child of length ell have absolute errors <= ell/1024, choose the child with the smaller estimated potential, tying to the left. The next potential is <= parent potential/2 + 1/32; eight replies suffice. | **Formal ingredient.** The arbitrary-interval potential error <= 1/64 is formalized. The recurrence, left tie rule and eight calls per round are proved for every round of the defined recursive selector under its reply contract. The paper states the one-step rule directly for an arbitrary interval. Replies are assumed; no value oracle is formalized.<br>[KE02.selector_estimate_error](../lean/KE02/SelectorGeometry.lean): For every positive-length interval and four replies within its tolerance, the estimated potential has absolute error <= 1/64.<br>[KE02.selector_potential_step](../lean/KE02/SelectorRecursion.lean): Potential recurrence along the defined scalar selector, for convex F and a valid reply stream.<br>[KE02.selector_choice_left](../lean/KE02/SelectorRecursion.lean): Actual approximate-reply estimates select the left child on equality.<br>[KE02.selector_choice_right](../lean/KE02/SelectorRecursion.lean): A strictly smaller right estimate selects the right child.<br>[KE02.selector_calls_count](../lean/KE02/SelectorRecursion.lean): The defined transcript has exactly 8j recorded calls after j rounds; this counts requests, not their evaluation cost. | [selector](#selector), [constants](#constants) |
| Proposition 5.3 — Interval selection yields a separating tilt<br>`prop:selector` | Start at [0,delta/n], take the least K with 2^K >= 16 n^3, and apply the approximate-value rule K times to F(t)=f(T+tX). The final midpoint c gives D=cX within budget and gap(T+D) > delta^4/(10^12 4096^4 n^42). | **Formal ingredient.** The scalar conclusion through final potential < 1/8, defect < r/8, nested intervals, least K, radius > delta/(4096 n^7), left ties and exactly 8K calls is formal. The specialization to eigenvalues and conversion of defect into a matrix gap remain paper proofs. Convexity, initial potential and reply accuracy are explicit formal hypotheses.<br>[KE02.selectorCertificate](../lean/KE02/SelectorProof.lean): For every n >= 2, 0 < delta < 1/2, convex real F on [0,delta/n], initial potential < n^3, and reply stream meeting the absolute-error contract: the full finite scalar transcript, interval and radius bounds, and final defect < r/8. Spectral interpretation, reply construction and arithmetic cost are absent. | [selector](#selector), [constants](#constants) |

## 6. Nearly linear evaluation in the exact arithmetic model

| Result | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Lemma 6.1 — Polynomial multiplication in permitted operations<br>`lem:multiply` | For every m >= 0, polynomials of degree <= m can be multiplied in O((m+1)[1+log(m+1)]) permitted exact operations, with the needed algebraic constants constructed from rational numbers using nonnegative square roots. | **Paper only.** The radix-two Fourier construction, half-angle constants, convolution correctness and uniform operation count are proved in the paper. No FFT or operation-count theorem is formalized or established by the finite checks.<br>No declaration cited. | Paper only. |
| Lemma 6.2 — Gap-independent spectral approximation<br>`lem:spectral-approximation` | For every Hermitian tridiagonal A with norm <= 1 and 0 < epsilon < 1, compute nondecreasing approximations to every ordered eigenvalue with absolute error <= epsilon/2 in O(n[1+log(n/epsilon)]^2) permitted operations, without simplicity or gap assumptions. | **Formal ingredient.** Lean proves the universal Graeffe and algebraic coefficient ingredients listed below. It does not prove the continuant-to-spectrum bridge, analytic ratio-root accuracy, sorting stability, spectral value oracle or operation count. The full spectral approximation lemma remains a paper proof.<br>[KE02.graeffeCertificate](../lean/KE02/GraeffeUniversal.lean): Even/odd coefficient reconstruction for every real polynomial; Graeffe root squaring for every finite real root list, including empty lists, zero roots and repetitions, at every natural iteration count.<br>[KE02.coefficientCertificate](../lean/KE02/CoefficientProof.lean): Coefficients of the actual product polynomial: expansion and leading coefficient; positivity, largest-product bounds and algebraic ratios for positive roots in decreasing order. The 2^k-th-root accuracy estimate is outside the statement. | [primitives](#primitives), [recursive](#recursive), [constants](#constants) |

## 9. Finite-bit construction and a uniform enclosure certificate

| Result | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Theorem 9.1 — Finite-bit diagonal regularization<br>`thm:finite-bit` | For n >= 2, d >= 2, delta=2^(-d), p and eta=2^(-p) as in Section 9.1, and a Hermitian tridiagonal proxy T0 on the eta grid enclosing each real input component within eta, a deterministic integer algorithm returns D=cX with 0 <= nc <= delta/4 and gap(T+D) > 2^(-100) delta^4/n^42 for every normalized T in that enclosure. Cost: O(n^2 p(1+log n)) operations on O(p)-bit integers, hence O(n^2 p^3(1+log n)) schoolbook bit operations; workspace and certificate size O(np), with p=O(log(n/delta)). | **Paper only.** The finite-information model, word-size, uniform gap and enclosure certificate theorems are proved in the paper. The constructor and independent rational verifier are tested on exact finite fixtures; these do not prove the uniform theorem or its cost. Verification may use longer integers; no bounded-word verification cost, nearly linear bit cost or floating-point stability theorem is asserted.<br>No declaration cited. | [finite-suite](#finite-suite), [finite-tests](#finite-tests), [finite-controls](#finite-controls) |
| Lemma 9.2 — Safeguarded integer inertia counts<br>`lem:bit-count` | For grid tridiagonal A and grid query x, integer LDL pivots use signed floor division and replace zero pivots by -1. There is a real diagonal E with norm <= eta such that the negative pivot count equals the number of eigenvalues of A+E below x, and A+E-xI is nonsingular. Thus count >= j implies lambda_j(A) < x+eta; count < j implies lambda_j(A) > x-eta. | **Paper only.** The uniform diagonal-error interpretation and inertia implications are proved in the paper. The perturbation E may depend on x. The finite suite exercises signed division, zero replacement and exact rational inertia branches; there is no Lean formalization of these recurrences or spectral implications.<br>No declaration cited. | [finite-tests](#finite-tests), [finite-suite](#finite-suite) |


## Polynomial ingredients within Section 6

These entries expose the formal core inside Lemma 6.2. They are not additional numbered paper results.

| Ingredient | Statement | Evidence and exact scope | Exact checks |
|---|---|---|---|
| Even/odd split and iterated root squaring<br>`eq:graeffe`, `eq:graeffe-roots` | For P(z)=product(z+r_i), the actual transform E(-z)^2+z O(-z)^2 is product(z+r_i^2); after k transforms the roots are powered by 2^k. | **Formal polynomial result.** Universal identities for real polynomials and every finite real root list, including the empty list, zeros and repeated roots. No positivity assumption or spectrum is used. Evaluation cost is outside the certificate.<br>[KE02.graeffeCertificate](../lean/KE02/GraeffeUniversal.lean): Even/odd coefficient reconstruction for every real polynomial; Graeffe root squaring for every finite real root list, including empty lists, zero roots and repetitions, at every natural iteration count. | [primitives](#primitives), [recursive](#recursive) |
| Largest-product and algebraic ratio bounds<br>`eq:coefficient-bounds`, `eq:root-estimates` | For positive roots in decreasing order, p_j <= e_j <= binomial(n,j) p_j <= 2^n p_j, and 2^(-n) r_j^(2^k) <= e_j/e_(j-1) <= 2^n r_j^(2^k). The ratio is the positive input to the root estimate. | **Formal polynomial result.** The coefficients come from an actual product polynomial. The formal coefficient and ratio inequalities quantify over every valid n,k,j. The equation defining q_j is an anchor for its algebraic input only; extracting roots, bounding their analytic error and their cost remain in the paper.<br>[KE02.coefficientCertificate](../lean/KE02/CoefficientProof.lean): Coefficients of the actual product polynomial: expansion and leading coefficient; positivity, largest-product bounds and algebraic ratios for positive roots in decreasing order. The 2^k-th-root accuracy estimate is outside the statement. | [primitives](#primitives), [recursive](#recursive) |
| Ratio roots and analytic spectral accuracy<br>`eq:root-ratio-bounds`, `eq:q-error` | Taking the 2^k-th root of the positive coefficient ratio gives r_j 2^(-n/2^k) <= q_j <= r_j 2^(n/2^k). For 1 <= r_j <= 3 and 2^k >= 6n/epsilon this yields absolute error <= epsilon/2. | **Paper only.** The analytic root step and uniform accuracy are outside the Lean core. Rational outward root intervals verified by exact power comparisons check finite examples only. The eigenvalue identification and sorting argument are also paper proofs.<br>No declaration cited. | [primitives](#primitives) |

## Exact computation commands

Run these commands from the repository root. The [single entry point](../verification/run.py) runs the mathematical checks and their rejection controls; see [VERIFICATION.md](../VERIFICATION.md).

### constants

Exact integer and rational comparisons for the inverse-gap constant, potential error, recurrence, radius, exponent and evaluator allowance. These arithmetic identities do not prove the symbolic inequalities or runtime.

```sh
python3 -B paper/check_constants.py
```

### primitives

Finite continuant/determinant comparisons, positive-root families, Graeffe transforms, algebraic ratios and rational outward root intervals. Includes repeated roots and rejection controls.

```sh
python3 -B verification/exact-real/verification/check_primitives.py
```

### selector

Ninety rational convex piecewise-linear functions and 8,064 bounded-error replies; exact secants, derivative-integral comparisons, child choices, radius and centered defect. Finite fixtures only.

```sh
python3 -B verification/exact-real/verification/check_convex_selector.py
```

### inverse

Nine rational eigenpair cases and separate rational fixtures for Wronskians, direction projectors, skipped rows, both truncation boundary entries, flattening, weight swaps and constants. These are supporting identities, not an all-input spectral proof.

```sh
python3 -B verification/exact-real/verification/check_inverse_tunneling.py
```

### recursive

Finite exact recursive polynomial and selector checks, including supplementary normalized characteristic identities that are not premises of the main construction.

```sh
python3 -B verification/exact-real/verification/check_recursive_primitives.py
```

### finite-suite

Authenticated integer-constructor and independent rational-certificate suite, including fixtures of orders 2,3,4,8, exact norm/enclosure checks and malformed-data rejection. Normal, optimized and alternate hash-seed outputs must agree. The uniform guarantee and cost remain paper proofs.

```sh
python3 -B verification/finite-precision/verification/run.py
```

### finite-tests

Exact tests of safeguarded count branches, independent rational inertia, proxy enclosure, construction and certificate data, including complex and zero edges. No numerical eigenvalue routine is used for acceptance.

The command below runs [run_tests.py](../verification/finite-precision/verification/run_tests.py) through its suite, which supplies its required output arguments.

```sh
python3 -B verification/finite-precision/verification/run.py
```

### finite-controls

Reason-specific malformed-certificate, bracket, defect and input-mismatch rejection checks. Passing finite controls is not a proof of the universal finite-bit theorem.

The command below runs [check_controls.py](../verification/finite-precision/verification/check_controls.py) through its suite, which supplies its required output arguments.

```sh
python3 -B verification/finite-precision/verification/run.py
```

## Remaining questions and formal boundaries

- The exact-real and finite-bit theorems use different input and cost models. A unit-cost exact square root does not imply a bounded-bit implementation.
- Nearly linear bit complexity for the full diagonal regularization problem remains open here. No stable floating-point implementation is proved.
- The scalar Lean selector assumes valid approximate replies, convexity and an initial potential bound. Exactly 8K recorded requests do not certify the cost or existence of the spectral value oracle.
- Hermitian spectral geometry, ordered-support quasimodes, small-gap-to-defect transfer, the continuant spectral interpretation, analytic ratio-root accuracy, sorting stability and both complete algorithmic cost arguments are proved in the paper only.
- Finite certificates guarantee the conclusion conditionally for every normalized matrix in their specified enclosure. A passing certificate does not establish that the normalized part of the enclosure is nonempty.
- The finite-bit construction has bounded word size. Its separate exact rational verifier may use longer integers; no bounded-word verifier complexity is claimed.
- The map checks references and inventory. The separate Lean verification command compiles proofs and checks axioms; the mathematical verification entry point executes exact checks and rejection controls.
