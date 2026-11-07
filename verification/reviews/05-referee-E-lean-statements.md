Reviewed: the Lean statements in lean/KE02/ (the structure `KE02.CoreCertificate` in lean/KE02/Statement.lean and the statement and definition modules it imports), against the final text in paper/, together with the scope claims in lean/README.md and lean/SCOPE.md.

# Referee report E: fidelity of the Lean statements to the final paper

Scope: the Lean STATEMENTS of `KE02.CoreCertificate` (lean/KE02/Statement.lean and
the statement/definition modules it imports) against paper/main.tex and main.pdf
("A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices",
28 pp.), together with the scope claims in lean/README.md and lean/SCOPE.md.
Proofs were not reviewed. No project file was changed.

## Reviewed objects (sha256)

* lean/KE02/Statement.lean: `3c047d4d3f492aa0fd7dac18dec84596c7f04312d8b1b259fd906e711333fcc1`
* lean/KE02/Algorithm2Statement.lean: `4ed93597f2d06a0ed458e50290a91c1cc394457bd88d283d3eec1871f575fced`
* lean/KE02/Algorithm2Definitions.lean: `5917772c14da593d6698c9284553ac5b1c4b640ae6cd29f9655ba5146668f60a`
* lean/README.md: `6d721b7eef589639be51fc2f80d662293bc7b2d08cc575b2ad34d4ca9220f944`
* lean/SCOPE.md: `70561ece5746e49c56f9763ded1cb79283aa40abfb5c351d8cb145f2589c021a`
* paper/main.tex: `6428c02567be443c2092c77294d90727c07539070297bf86a60c27b713fd40ec`
* paper/main.pdf: `a8b92e6045e6c18ecde4e9186a7bdb736c446a9aee790792e42be2017cba5001`

## Checks performed

* Each of the 19 entries in audit/statement-hashes.json and the 47 entries in
  audit/source-hashes.json matches the files reviewed.
* `lake build` was run on a copy of the project. The build completed (3141 jobs).
* `#print axioms KE02.coreCertificate` gives `[propext, Classical.choice, Quot.sound]`.
* `#print KE02.CoreCertificate` shows exactly the nine fields of Statement.lean.
* `#check Algorithm2Certificate.run` matches the source text.
* An exact-oracle instantiation of `run` elaborates.
* `doublingExponent (16 n^3)` evaluates, for n = 0..11, to
  [0, 4, 7, 9, 10, 11, 12, 13, 13, 14, 14, 15]. These are the least K with
  $`2^K \ge 16n^3`$.
* Grep of all statement and definition files finds no `instance`, `notation`,
  `macro`, `syntax`, `attribute`, `set_option`, `opaque`, `axiom`, `sorry` or
  `local`. Nothing can change the meaning of the operators, and no predicate is
  opaque.
* Equation and page numbers were taken from the compiled PDF text. The labels
  are: (24) and (25) are the two input matrices in Example 3.2; (26) is Lemma 3.2's
  nuclear bound; (27) is $`S^{\mathrm{aux}} \ge 1`$; (28) is the nuclear-duality bound.

## Verdict: ACCEPT WITH CHANGES

All changes are wording in the README, SCOPE and two docstrings; no Lean
statement needs to change.

* Statements: every field of `CoreCertificate` matches its paper statement
  exactly or is more general.
* Transcript: Algorithm 2 follows the paper line by line. It uses the real
  replies, the seven points plus one midpoint, the paper's tolerances, and ties
  going left.
* `K` and `k` are the paper's choices and are proved to be found by doubling.
* The premises of `run` can be satisfied.
* Nothing claims Theorem 1.1 or the gap theorem (38) as formalized.
* The SCOPE "Not formalized" list is complete.

## 1. Definitions (literalness)

| Lean | Plain mathematics | Paper | Judgement |
|---|---|---|---|
| `secant F u v` | (F v - F u)/(v - u) | (9), p. 6, l. 531 | EXACT (used only for $`u < v`$) |
| `centeredVariation F h t` | (F(t+h)-F t)/h - (F t-F(t-h))/h | (13), p. 6, l. 623 | EXACT |
| `endpointVariation F θ h t` | (F(t+h)-F(t+(1-2θ)h))/(2θh) - (F(t-(1-2θ)h)-F(t-h))/(2θh), any real θ | (33), p. 16, l. 1716 | EXACT; each statement carries its θ range |
| `centeredEstimate`, `endpointEstimate` | same formulas on given reals (the replies) | the hatted S of Alg. 1/2 | EXACT |
| `Oracle = ℕ → ℝ → ℝ → ℝ`, `Query` | request i at point x with tolerance τ receives O i x τ; log stores (point, tol, reply) | Alg. 2 "evaluate ... to absolute error" | EXACT. Alg. 2 is deterministic, so every adaptive reply strategy is such a function. The logged reply is the value that is used. |
| `alg2K n` | least K ∈ ℕ with 16n³ ≤ 2^K (Nat.find) | Alg. 2 line 1, l. 1762, p. 17 | EXACT |
| `doublingSearch` / `doublingExponent` | compare target ≤ p, otherwise double p and increment k; start p = 1, k = 0; fuel = target | "by doubling and comparisons" | EXACT (the fuel exists only for termination and is never exhausted) |
| `alg2Theta n` | 1/(4K) in ℝ | Alg. 2 line 1 | EXACT |
| `refinePoint θ h t` | t-2h, t-2h+2θh, t-2θh, t, t+2θh, t+2h-2θh, t+2h (h = updated radius) | proof of Thm 4.2, l. 1945-1950 | EXACT (all 7 points checked) |
| `selectCenter` | t-h if left ≤ right, else t+h | Alg. 2, l. 1777-1781 | EXACT (ties go left) |
| `alg2Init` | t = h = δ/(2n); requests 0, 1, 2 at t-h, t, t+h with tol h/256; computes the centered estimate | Alg. 2, l. 1765-1766 | EXACT |
| `alg2Step` | h ← (1/2-θ)h; τ = 2θh/256; 7 requests at refinePoint; left/right endpoint estimates from replies 0-3 and 3-6; select; 1 request at the new centre; centered estimate at the new centre from replies (0, m, 3) or (3, m, 6) | Alg. 2, l. 1771-1789 | EXACT |
| `alg2Loop` / `alg2Run` | test (estimate $`+\ 1/64 < 1/2`$), then up to K passes, each followed by a test (K+1 tests in all); `returned = false` only if the test after the K-th pass fails | Alg. 2, for j = 0..K-1 | EXACT |
| `alg2State O n δ j` | j-fold alg2Step from alg2Init, without tests | names $`(t_j, h_j)`$ | EXACT |
| `triangleWeight` | max(1 - abs(x-t)/h, 0) | proof of Lemma 4.1, l. 1546 | EXACT |
| `basicK n` | least $`K_b`$ with $`16n^3 \le (3/2)^{K_b}`$ | Alg. 1, l. 1441 | EXACT |
| `basicPoint h t` | t-2h, t-h, t, t+h, t+2h | Alg. 1, l. 1450 | EXACT |
| `evenPart`, `oddPart`, `graeffe` | E and O with P = E(z²)+zO(z²); G(P) = E(-z)² + z O(-z)² | App. A, l. 2669-2671 | EXACT |
| `rootPolynomial r` | $`\prod(X + r_i)`$ | App. A | EXACT |
| `elementaryCoeff r k j` | coeff of $`X^{n-j}`$ in $`\prod(X + r_i^{2^k})`$ | $`e_j`$, App. A | EXACT |
| `leadingRootProduct r k j` | $`\prod_{i<j} r_i^{2^k}`$ (0-based) | $`p_j`$, l. 2676 | EXACT |
| `graeffeCoeff r k j` | coeff of $`X^{n-j}`$ in the actual k-th Graeffe iterate | $`e_j`$ | EXACT |
| `rootEstimate` | $`(e_{i+1}/e_i)^{1/2^k}`$ (rpow) | the hatted $`r_j`$, l. 2689 | EXACT (0-based shift stated) |
| `iteratedSqrt k` | sqrt applied k times | "k successive square roots" | EXACT |
| `graeffeSteps n η` | least k with 8n/η ≤ 2^k | App. A, l. 2683 | EXACT for $`\eta > 0`$ (`steps_least`) |
| `graeffeDoubling` | doubles R from 1, compares 8n ≤ Rη | App. A, l. 2684-2686 | EXACT |
| `tridiag`, `continuant` | standard tridiagonal matrix; $`Q_{k+2} = a_{k+1}Q_{k+1} - b_k c_k Q_k`$ | App. A | EXACT |
| `charRecurrence A` | $`P_0 = 1`$, $`P_1 = X+2+a_1`$, $`P_i = (X+2+a_i)P_{i-1} - A_{i-1,i}A_{i,i-1}P_{i-2}`$ | App. A, l. 2655-2656 | EXACT for real symmetric A ($`c_i = A_{i,i+1}A_{i+1,i} = A_{i,i+1}^2`$); STRONGER (any real tridiagonal A) |

## 2. Fields of CoreCertificate

### 2.1 endpoint : EndpointCertificate (pp. 6, 16-17)

| Field | Lean says | Paper | Judgement |
|---|---|---|---|
| `centered_nonneg` | ∀ convex F : ℝ→ℝ, $`h > 0`$, t: $`S_h(t) \ge 0`$ | (13), l. 623 | EXACT |
| `endpoint_nonneg` | convex, $`0 < \theta \le 1/2`$, $`h > 0`$ ⇒ $`S_h^{(\theta)}(t) \ge 0`$ | text after (33), l. 1722 | EXACT |
| `centered_le_endpoint` | convex, $`0 < \theta \le 1/2`$, $`h > 0`$ ⇒ $`S_h \le S_h^{(\theta)}`$ | (34), l. 1739 | EXACT |
| `child_windows` | ring identities: children are [t-(1-2θ)h, t] and [t, t+(1-2θ)h] | l. 1748-1752 | EXACT (trivial identity) |
| `points_in_parent` | $`0 < \theta \le 1/4`$, $`h > 0`$ ⇒ the 7 points for h' = (1/2-θ)h lie in [t-h, t+h] | proof of Thm 4.2, l. 1918-1922 | EXACT |
| `points_of_children` | child variations = endpointEstimate on F at refinePoint 0-3 and 3-6 | l. 1945-1950 | EXACT (definitional) |
| `children_sum` | convex, $`0 < \theta \le 1/4`$, $`h > 0`$ ⇒ sum of child variations ≤ parent | proof of Lemma 4.2, l. 1846-1853 | EXACT |
| `contraction` | same premises ⇒ $`\min(\text{children}) \le \tfrac12 S_h^{(\theta)}(t)`$ | (35), l. 1806 | EXACT |
| `estimate_error` | $`\theta > 0`$, $`h > 0`$, four replies within 2θh/256 ⇒ error ≤ 1/64 | proof of Lemma 4.2, l. 1860-1865 | EXACT |
| `ties_left` | selectCenter h t e e = t - h | Alg. 2 "if ≤" | EXACT |
| `potential_step` | convex, $`0 < \theta \le 1/4`$, $`h > 0`$, seven actual replies within 2θh'/256 ⇒ $`S_{h'}^{(\theta)}(\text{selected}) \le \tfrac12 S_h^{(\theta)}(t) + 1/32`$ | (36), l. 1817, for one step | EXACT |

### 2.2 algorithm2 : Algorithm2Certificate (pp. 17-20)

| Field | Lean says | Paper | Judgement |
|---|---|---|---|
| `K_spec` | $`16n^3 \le 2^K`$ and $`2^k < 16n^3`$ for every $`k < K`$ | l. 1762 | EXACT |
| `K_doubling` | doublingExponent(16n³) = K for every n | "by doubling" | EXACT |
| `K_ceil_log` | n ≥ 1 ⇒ K = ⌈log₂(16n³)⌉₊ | l. 1746, 1880 | EXACT |
| `K_upper` | n ≥ 1 ⇒ $`2^K < 32n^3`$ and K ≥ 1 | l. 1932 | EXACT |
| `theta_range` | $`0 < \theta \le 1/4`$ and 1/2 - θ = ½(1 - 1/(2K)) | l. 1929-1931 | EXACT |
| `bernoulli` | K ≥ 1 ⇒ (1 - 1/(2K))^K ≥ 1/2 | l. 1932 | EXACT |
| `LK_bound` | $`\delta/(64n^4) < (\delta/n)(1/2-\theta)^K`$ | l. 1928-1931 | EXACT |
| `main_bound_form` | n ≥ 1, $`0 < \delta < 1`$ ⇒ 2⁻³⁴(δ/n)¹² ≤ 2⁻³⁴δ²/n¹² | second inequality of (5), l. 192-198; proof l. 2087 | EXACT |
| `stopping_constants` | $`1/8 + 1/128 + 1/64 < 1/2`$ | l. 1906-1912 | EXACT |
| `midpoint_estimate_error` | $`0 < \theta \le 1/4`$, $`h > 0`$, three replies within 2θh/256 ⇒ error ≤ θ/32 ≤ 1/128 | l. 1907-1910 | EXACT |
| `run` | ∀ n ≥ 1, $`\delta > 0`$, convex F with (9) for all $`u < v`$, every oracle O whose replies to the requests in the actual log of alg2Run O n δ are within the requested tolerance ⇒ Algorithm2Outcome | Thm 4.2, l. 1875-1898, without (38) | EXACT relative to Lemma 2.1 used as a premise; more general than the paper (n ≥ 1 and $`\delta > 0`$ instead of n ≥ 2 and $`\delta < 1/2`$) |
| `premises_satisfiable` | ∀ n ≥ 1, $`\delta > 0`$: some F and O meet all premises | — | witness of non-vacuity. The premises also hold for every admissible F with the exact oracle, because all tolerances are positive. |

Fields of Algorithm2Outcome (run r = alg2Run O n δ):

| Field | Paper | Judgement |
|---|---|---|
| `returns`, `refinements_le` | "terminates after at most K refinements" | EXACT |
| `state_eq`, `earlier_tests_fail`, `returned_test_passes` | returns at the first successful test | EXACT |
| `radius_formula` (∀ j) | $`h_j = (1/2-\theta)^j\,\delta/(2n)`$ | EXACT |
| `windows_inside`, `windows_nested` (∀ j) | l. 1914-1918 | EXACT (holds for all replies) |
| `initial_potential` | $`S^{(\theta)}_{h_0}(t_0) < n^3`$ from (9), used at l. 1902 | EXACT |
| `potential_step` ($`j <`$ refinements) | (36) along the run | EXACT |
| `potential_bound` (j ≤ refinements) | iterated (36), l. 1903 | EXACT |
| `potential_final` | $`S^{(\theta)}_{h_K}(t_K) < 1/8`$ if K refinements are made | EXACT |
| `estimate_accuracy` | error of the hatted $`S_h(t)`$ ≤ 1/64 at the returned test | WEAKER than the paper's θ/32 at refinement tests, but it is exactly what $`S_h(t) < 1/2`$ needs; the θ/32 bound is a separate field. Not a defect. |
| `centered_lt_half`, `radius_lower` | (37), l. 1882 | EXACT |
| `radius_upper`, `radius_lt_one` | $`h \le \delta/(2n) < 1`$, l. 1937 | EXACT |
| `window`, `budget` | [t-h, t+h] ⊆ [0, δ/n]; 0 ≤ t and nt ≤ δ | EXACT (the scalar part of ‖D‖₂ ≤ δ; ‖tX‖₂ = nt is not formalized) |
| `queries_inside` | every evaluation point is in [0, δ/n], l. 1921 | EXACT (and tolerance $`> 0`$) |
| `tolerance_upper`, `tolerance_lt_one` | $`\varepsilon < 1`$ in the proof of Thm 1.1, l. 2091 | EXACT |
| `calls_exact`, `calls_le` | 3 + 8j requests, at most 3 + 8K, l. 1897 and 1943-1953 | EXACT (length of the actual log) |
| `gap_scale` | $`h^2/(2^{20}n^4) > 2^{-34}\delta^2n^{-12}`$, the scalar step of (38), l. 1938-1940 | EXACT as a scalar; (38) itself is not formalized |
| `min_accuracy` | (40), l. 2066 | EXACT (every tolerance $`> \delta/(2^{16}Kn^4)`$) |

### 2.3 basicSelector (pp. 14-16)

| Field | Paper | Judgement |
|---|---|---|
| `weights` | proof of Lemma 4.1, l. 1550-1552 | EXACT |
| `weights_attained` | sharpness of 4/3 (not claimed in the paper) | additional fact, correct |
| `children_sum` | proof of Lemma 4.1 ("taking half the sum") | EXACT, for every convex F |
| `contraction` | (29), l. 1509 | EXACT |
| `estimate_error` | l. 1559-1568 | EXACT |
| `step` | (30), l. 1523: one refinement of Alg. 1 with five actual replies within (h/4)/256, ties left | EXACT for one step |
| `initial` | $`S_{h_0}(t_0) < n^3`$ from (9), l. 1636 | EXACT (for every $`h > 0`$ and t) |
| `Kb_spec`, `Kb_ceil` | Alg. 1 l. 1441; Thm 4.1 l. 1603 | EXACT |
| `first_term`, `iterate`, `geometric`, `final`, `stopping_constants` | l. 1638-1660 | EXACT (for an abstract sequence satisfying the recursion) |
| `calls` | "at most $`3 + 5K_b`$ evaluations", l. 1615 | TRIVIAL conclusion: $`j \le K_b \Rightarrow 3+5j \le 3+5K_b`$, not linked to any evaluation count. SCOPE describes it correctly; the README lists it as a proved item of Theorem 4.1 (Change 1). |
| `radius_lt_one` | $`h \le \delta/(2n) < 1`$, l. 1667 | trivial arithmetic on $`(\delta/(2n))4^{-j}`$; labelled honestly |
| `radius` | (32), l. 1693, for every radius $`(\delta/(2n))4^{-j}`$ with $`j \le K_b`$ | EXACT in scalar form (the bound for the returned h of a run is not formalized, as stated) |

### 2.4 graeffe, coefficients, rootExtraction, continuant (App. A, pp. 27-28; Sec. 4.3, p. 19)

* **graeffe**: `even_coeff`, `odd_coeff`, `reconstruct`, `one_step` and `iterate`
  state the split P = E(z²) + zO(z²), the identity $`G(\prod(X+r_i)) = \prod(X+r_i^2)`$, and
  the k-fold iterate, for all real roots (l. 2669-2675). EXACT, and more general
  (no positivity needed).
* **coefficients**: all EXACT.
  * `expansion` (Vieta), `leading` ($`e_0 = 1`$) and `positive`.
  * `bounds`: $`p_j \le e_j \le C(n,j)\,p_j \le 2^n p_j`$ for positive nonincreasing roots and
    j ≤ n (l. 2675-2677).
  * `ratio_bounds`: $`r_i^R/2^n \le e_{i+1}/e_i \le 2^n r_i^R`$.
* **rootExtraction**:
  * `graeffe_coeff` and `coeff_bounds`: EXACT.
  * `ratio_root`: (43), l. 2678. EXACT.
  * `iterated_sqrt` and `two_rpow_sub_one_le`: EXACT.
  * `root_error`: the error of the hatted r is ≤ 4n/R, given $`0 < r < 4`$ and
    n ≤ R (l. 2689-2690). EXACT.
  * `steps_least`, `steps_doubling` and `steps_choice`: the least k with
    Rη ≥ 8n, found by doubling R from 1, and $`8n/\eta \le R < 16n/\eta`$ and
    4n/R ≤ η/2 (l. 2683-2690). EXACT.
  * `weighted_error`: errors ε/(2Σj) give error ≤ ε. EXACT.
  * `sum_error`: the remark after Lemma 4.3, l. 2042-2046. EXACT.
  * `pipeline`: given n ≥ 1, roots in (0, 4) in nonincreasing order and
    $`0 < \varepsilon < 1`$, with η = ε/Σj and k = graeffeSteps (equal to the doubling
    result):
    * $`\lambda_j := r_{n+1-j} - 2`$ is nondecreasing;
    * each hatted $`\lambda_j`$, computed from k square roots of the actual coefficient
      ratio, is within η/2;
    * the weighted sum is within (n(n+1)/2)(η/2) ≤ ε (l. 2696-2706).

    EXACT, given the premises $`r_{n+1-j} = 2 + \lambda_j(A)`$ and $`r_j \in (0, 4)`$, which
    SCOPE declares.
* **continuant**:
  * `det_tridiag`: holds for every CommRing R with R : Type. The paper does not
    state it for a general ring. It is correct, but the README wording "any
    commutative ring" is too broad, because only universe 0 is covered.
  * `det_char`: for every real A that vanishes outside the tridiagonal band,
    det(XI + 2I + A) = charRecurrence A n in ℝ[X] (l. 2653-2656). EXACT, and
    STRONGER (A need not be symmetric).
  * `symmetric_coeff`: EXACT.
  * The complex Hermitian $`c_i`$ is not formalized, as stated.

### 2.5 localConstants (pp. 9-13, 18)

All fields are real inequalities or identities with explicit premises. Each
matches the paper step cited in SCOPE:

* `discarded_rows`: Step 1, l. 943.
* `direction_gap`: (21).
* `tau_le`: Step 3, l. 1037.
* `case_a`: trivial.
* `case_c`: l. 1083-1094, with τ ≤ 1.
* `total_change`: l. 1107-1113.
* `truncation`: Step 4, l. 1144-1149.
* `nuclear`: proof of (26), l. 1324-1330.
* `gamma_range`: proof of Prop. 3.1, l. 1347.
* `aux_variation`: the quotient in (27) is (13).
* `transfer`: (28) at three points gives $`S_h \ge S^{\mathrm{aux}} - (4n/h)N`$; (28) itself is a
  hypothesis.
* `constant`: 5/8.
* `chain`: the full scalar chain.
* `gap_chain`: l. 1938-1940.

Each is EXACT as a scalar fact. The README says "scalar steps", and SCOPE states
that the matrix statements are not formalized.

### 2.6 wronskian (p. 10)

* `identity`: (22), l. 997-1004. It assumes real sequences with $`\beta_0 = 0`$ that
  satisfy the coordinate equations of Step 2 for 1 ≤ i ≤ n, and concludes (22)
  for every i ≤ n. STRONGER than the paper: $`\beta_n`$, $`a_{n+1}`$ and $`b_{n+1}`$ are free,
  and the paper's case $`\beta_n = 0`$ is an instance.
* `partial_inner`: the Cauchy-Schwarz bound, the absolute value of the partial
  sum $`\sum_{j\le i}`$ is at most 1/2 (l. 1009-1016). EXACT.
* `bound`: $`\lvert\beta_i\rvert\,\lvert\det\rvert \le \gamma/2`$. EXACT.

## 3. README / SCOPE claims

* Every row of the README "What is proved" table matches a Lean field. I checked
  each item. The page numbers are correct (Thm 1.1 p. 2 / proof p. 20, (13) p. 6,
  (33) p. 16, Lemma 4.2 p. 17, Thm 4.2 p. 18, (40) p. 19, Lemma 4.1 p. 14,
  Thm 4.1 p. 15, Remark 4.1 p. 16, (22) p. 10, Lemma 3.1 p. 9, Lemma 3.2 p. 12,
  (28) p. 13, App. A pp. 27-28).
  * The one overclaim is "$`3 + 5K_b`$" (Change 1).
  * One wording is ambiguous: "Section 4.3 (Lemma 4.3 and the remark after it)"
    (Change 2).
* The SCOPE "Not formalized" list is complete. It covers:
  * all spectral theory: Lemma 2.1, (7)-(12), (14), (15), Hellmann-Feynman and
    Remark 1.1;
  * the conclusions of Lemma 2.1 used as premises (Definitions section);
  * Section 3 as matrix statements: Lemmas 3.1 and 3.2, (27), (28) and Prop. 3.1;
  * the gap conclusions of Thms 4.1 and 4.2, and ‖tX‖₂ = nt;
  * the transcript of Algorithm 1;
  * the oracle of Lemma 4.3 and the arithmetic model;
  * all cost and complexity bounds;
  * $`P(z) = \prod(z + r_j)`$;
  * the complex Hermitian $`c_i`$;
  * FFT and roots of unity;
  * bit complexity;
  * numerics and examples.

  I found no further paper statement missing from the list.
* The short README paragraph "Not formalized from Theorem 1.1" does not say that
  Lemma 2.1 (convexity and (9)) enters as a premise, and does not mention
  Section 3. SCOPE does (Change 3).
* SCOPE says that "the existence of replies meeting the error premise" is not
  formalized. This is inaccurate: such replies trivially exist, and
  `premises_satisfiable` proves it. What is not formalized is that the Lemma 4.3
  procedure produces them (Change 4).
* No sentence claims that Theorem 1.1 or the gap theorem is formalized. Two Lean
  docstrings label scalar facts with matrix-result numbers (Change 5).

## 4. Verdict and changes

Verdict: ACCEPT WITH CHANGES. All changes are wording in the README, SCOPE and
two docstrings; no Lean statement needs to change. File paths below are relative
to lean/.

1. `README.md:29` lists "`3 + 5K_b`, `h ≤ δ/(2n) < 1`" as proved for Theorem 4.1.
   But `BasicSelectorStatement.lean:66` (`calls`) is the trivial
   `j ≤ K_b → 3+5j ≤ 3+5K_b`. Reword to "the arithmetic facts `3+5j ≤ 3+5K_b`
   ($`j \le K_b`$) and `(δ/(2n))4^(−j) ≤ δ/(2n) < 1` (the evaluation count of
   Algorithm 1 is not formalized)", or drop the field.
2. `README.md:32`: "Section 4.3 (Lemma 4.3 and the remark after it), the bound
   `n(n+1)η/2`" → "Section 4.3, the remark after Lemma 4.3: the bound
   `n(n+1)η/2` (Lemma 4.3 itself is not formalized)".
3. `README.md:37–40`: add "Lemma 2.1 is not formalized: convexity of `F` and the
   secant bounds (9) are premises; Lemmas 3.1–3.2 and Proposition 3.1 enter only
   through scalar steps."
4. `SCOPE.md:88–89` and `SCOPE.md:189–190`: "the existence of replies
   meeting/satisfying the error premise" is wrong, since exact replies trivially
   exist and `premises_satisfiable` proves it. Replace with "that the procedure of
   Lemma 4.3 / Appendix A, applied to `F(t) = Σ_j jλ_j(T+tX)`, produces replies
   meeting the error premise".
5. `KE02/Algorithm2Statement.lean:81`: docstring "(38): …" → "The scalar
   inequality used for (38): … (the gap bound (38) is not formalized)". `:104`:
   "Theorem 1.1, (5): …" → "The second inequality of (5): …". This means
   re-pinning `audit/statement-hashes.json`, `audit/source-hashes.json` and the
   digests inside `audit/verify.py`.
6. Optional, `README.md:25` and `SCOPE.md:84`: "accuracies in `[ε_min, 1)`" is
   circular at the lower end, because $`\varepsilon_{\min}`$ is by definition the smallest
   requested accuracy. State what is proved: `δ/(2¹⁶Kn⁴) < ε < 1` for $`\delta < 1/2`$,
   i.e. (40) and $`\varepsilon < 1`$.
7. Optional, `README.md:33` and `ContinuantStatement.lean:13`: "over any
   commutative ring" → "any commutative ring `R : Type`" (Lean only quantifies
   over `Type`).

Minor findings that need no change:

* `estimate_accuracy` gives 1/64 rather than the paper's θ/32, but that is all
  `S_h(t) < 1/2` needs, and θ/32 is a separate field.
* (22) and the continuant recurrence are stated more generally than in the paper.
