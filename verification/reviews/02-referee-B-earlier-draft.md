Reviewed: an earlier 27-page draft of the paper (main.tex and main.pdf), against the catalogue statement of KE-02.

# Referee report B (adversarial): earlier draft of the paper

Own view formed first, then compared with an earlier version of the argument.

## Verdicts

- (i) Gap theorem (Thm 4.2, $`\mathrm{gap}(T+tX) > 2^{-34}\delta^2 n^{-12}`$, $`t \in [0, \delta/n]`$): ACCEPT WITH
  CORRECTIONS (editorial only; every inequality checks; no counterexample).
- (ii) Full KE-02 target including complexity: ACCEPT WITH CORRECTIONS — the oracle is proved in App. A
  (characteristic polynomial, Graeffe squaring, coefficient ratios), so the cost bound is unconditional, but abstract
  and conclusion word it as conditional (corr. 2). $`a=12`$, $`c_0=2^{-34}`$, $`q=3`$ (paper says $`q=4`$).
  Architecture matches the earlier version of the argument (same F, same eigenvector-weight swap, same oracle); real
  gains: $`O(n\sqrt{\gamma})`$ residual in the localization lemma and selector child radius $`(1/2-\theta)h`$ instead
  of $`h/4`$.

## Steps

Steps S1–S12 all hold:

- Lemma 2.1 (Ky Fan convexity, variational formula, secant slopes in $`[n(n+1)/2,\ n^2(n+1)/2]`$, $`S < n^3/2`$);
- Lemma 3.1 Steps 1–4 (discarded mass $`\le 1/4`$, $`\sum r_i^T r_i \ge (3/4)I`$, sin angle $`\ge \sqrt{3/8}`$;
  Wronskian sign and telescoping; $`\tau \le 1/(4\sqrt n)`$; case (c) bound
  $`2\gamma/\tau^2 + \gamma/2 \le 2.5\,\gamma/\tau^2`$; at most $`n-1`$ steps of $`5/(16n)`$; $`[H, P_L]`$ boundary
  terms; residual $`\le 16n\sqrt{\gamma}`$; X-gap $`\ge 1`$);
- Lemma 3.2 (nuclear norm $`\le 96n\sqrt{\gamma}`$; weight swap gives $`S^{\mathrm{aux}} \ge 1`$);
- Prop 3.1 ($`S_h \ge 1 - 384n^2\sqrt{\gamma}/h = 5/8`$; covers zero edges and repeated eigenvalues);
- Lemma 4.1/Thm 4.1 (4/3 contraction; final $`S < 5/32`$);
- Lemma 4.2 (ordered secants; 1/64 per error);
- Thm 4.2 ($`S^{\theta} < 1/8`$; $`2^K < 32n^3`$; $`h > \delta/(128n^4)`$; $`2^{-14}\cdot2^{-20} = 2^{-34}`$; $`3+8K`$
  evaluations);
- §4.3 (smallest accuracy $`> \delta/(2^{16}Kn^4)`$);
- App. A (product tree $`O(n\log^2 n)`$; FFT roots from half-angle square roots; $`G(P)(z) = \prod(z + r_j^2)`$;
  $`p_j \le e_j \le 2^n p_j`$; error $`4n/R \le \eta/2`$; per call $`O(n[1+\log(n/\varepsilon)]^2)`$).

## Corrections

1. Constant: abstract and eq. (1.5) "$`c\,\delta^2 n^{-12}`$" with $`\ge`$ → "$`> 2^{-34}\delta^2 n^{-12}`$"
   (equivalently $`\ge 2^{-34}(\delta/n)^{12}`$); the constant in the code repository README concerned the repository
   contents at the time of review (valid but weaker) — align it with the paper (release precondition).
2. Remove the oracle hedge in abstract and §6 first paragraph; mention the alternative route only as an alternative.
3. Add one main theorem in §1 combining Thm 4.2 and Lemma 4.3 (deterministic, $`\lVert D\rVert \le \delta`$, gap
   bound, $`O(n[1+\log(n/\delta)]^3)`$ operations); $`q=3`$ in §4.3; Lemma 4.3 per-call bound ^2.
4. App. A: k and K found by doubling and comparison ($`R\eta \ge 8n`$, $`2^K \ge 16n^3`$), no logarithm or floor of a
   real input; complex arithmetic as pairs of reals; complex edges enter only through $`\lvert\beta_i\rvert^2`$ (no
   phase gauge computed); fix $`r_j`$ labelling; matching of ratios to eigenvalues is index-wise by (A.1).
5. Lemma 3.1 Step 3: "at most $`q-p \le n-1`$ steps, each $`\le 5\gamma/\tau^2 = 5/(16n)`$"; triangle inequality for
   projector differences.
6. Lemma 3.2: spell out $`\lVert AQ\rVert_*, \lVert QA\rVert_*, \lVert QAQ\rVert_* \le \sqrt2\,\lVert AQ\rVert_F`$.
7. Thm 4.2: state $`[t-h, t+h] \subseteq [0, \delta/n]`$.
8. §5 numerics: evidence, not proof; $`j^*`$ is the first certified stop along an uncertified double-precision path;
   caption and §1 phrase "rigorously certified numerical experiments" should say so; code only "on request".
9. Remark: certificate is lossy ($`n=2`$ at a crossing: $`S_h < 1/2`$ iff $`\mathrm{gap} > 3h/4`$; search never found
   $`\mathrm{gap}/h < 1/2`$).

## Independent tests

- Exact-rational Algorithms 1–2 on diagonal T incl. zero edges, repeated eigenvalues, H = multiple of I, n = 2..12,
  three deltas, exact/random/adversarial errors (brute force over sign patterns) — 1188 runs all hold.
- Algorithm 2 on tridiagonal families (random, complex phases, Toeplitz, Wilkinson, avoided crossings 1e-9..1e-5,
  glued blocks, zero edges), n = 2..16, re-checked in mpmath — 339 runs pass ($`\le 6`$ of $`K=16`$ steps;
  $`\min\ \mathrm{gap}\,n^2/\delta = 0.32`$).
- Synthetic convex F with maximal slope variation, $`n \le 100`$ — $`\le K-5`$ steps.
- Lemmas 3.1/3.2 literally on 377 near-degenerate cases (gaps to ≈ 1e-16): residual $`\le 0.60`$ of bound, nuclear
  norm $`\le 0.16`$ of bound, X-gap $`\ge 1`$, $`S^{\mathrm{aux}} \ge 1`$.
- Quantitative $`S_h \ge 1 - 384n^2\sqrt{g}/h`$ for $`h \in [10^{-6}, 1]`$ (min slack 0.069).
- Nelder–Mead counterexample search n = 3..6 (60 restarts): min $`\mathrm{gap}/h = 0.50`$ vs threshold ≈ 1e-9 — none.
- App. A exact (product tree = recurrence, $`G(P)(-z^2) = P(z)P(-z)`$, positivity, (A.1), F error $`\le \varepsilon`$),
  12 cases.
- The paper's Table and Examples 2.3, 3.1, 3.2 reproduced.
