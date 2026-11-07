Reviewed: the final text in paper/ (main.tex, main.pdf, refs.bib; 28 pages), against the catalogue statement of KE-02, including a check of the corrections made since the earlier draft.

# Referee report C: "A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices" (W. Zhu, P. Nie), final text

**Verdicts:** (i) gap theorem (Prop. 3.1 + Thm 4.2, $`\mathrm{gap} > 2^{-34}\delta^2 n^{-12}`$): **ACCEPT**. (ii) full KE-02 target, including the operation count (Thm 1.1 + App. A, $`a=12`$, $`c_0=2^{-34}`$, $`q=3`$): **ACCEPT WITH CORRECTIONS** (wording only). No mathematical gap or error found. Own exact checker: 55 checks pass, 7/7 negative controls rejected, identical output under `python -O`. One control shows Prop. 3.1 fails for a 3×3 non-tridiagonal T, so the tridiagonal hypothesis is really needed. Items 1–13 and fixes (a)–(f) of the list of corrections are applied in the paper; items 5–6 concern the code repository.

**Reviewed files (sha256)**
- paper/main.tex `6428c025…40ec` (2719 lines)
- paper/main.pdf `a8b92e60…5001` (28 pp.)
- paper/refs.bib `6d1c8087…`
- the catalogue statement of KE-02 (catalogue README, fetched 2026-11-07)

**Read before the derivation:** only the catalogue KE-02 statement and the paper: main.tex in full, `matrix_with_cut.tex`, `vectors_with_cut.tex`, refs.bib, and the extracted text of main.pdf (used only for numbering and references). The referee's derivation was written from these sources alone.

**Consulted afterwards:**
- The earlier 27-page draft (PDF and source; the draft recorded in the change record), used for a line diff.
- The list of corrections and the change record.
- Read-only, for public readiness only: the code repository linked from the paper, the authors' public numerics code (to check Table 2), and the cited Sobczyk v2.
- No other referee's report.

## 1. Target fidelity

- **Matrix class and normalisation:** n ≥ 2, Hermitian tridiagonal $`T \in \mathbb{C}^{n\times n}`$, ‖T‖₂ ≤ 1, δ ∈ (0, 1/2), input is the three diagonals. Thm 1.1 (185–209) matches.
- **Perturbation:** D = tX with X = diag(1..n) and t ∈ [0, δ/n], so ‖D‖₂ = nt ≤ δ. This is a one-parameter subfamily of the allowed real diagonal D. Forming D costs n multiplications, which is not stated (correction 6).
- **Gap bound:** $`\mathrm{gap} > 2^{-34}\delta^2 n^{-12} \ge 2^{-34}(\delta/n)^{12}`$, i.e. $`c_0 = 2^{-34}`$ and $`a = 12`$. gap is the minimal difference with multiplicity in both texts.
- **Cost:** O(n[1+log(n/δ)]³) with absolute constants, so q = 3.
- **Model:** exact arithmetic and comparisons, unit-cost square roots of nonnegative reals, complex numbers as pairs of reals. App. A uses only +, −, ×, ÷, comparisons and square roots of nonnegatives (half-angle roots of unity; R-th roots by k square roots).
  - The sentence "no logarithm or floor of a real input is computed" is literally inaccurate (correction 1).
  - The Graeffe oracle works with numbers of magnitude about $`4^{nR}`$, $`R = \Theta(n^3/\varepsilon)`$. The model permits this, and it is disclosed (2711–2712; correction 2).
- **Deterministic:** tie rule "≤ ⇒ left" (1781–1786).
- **Not claimed:** bit or finite-precision complexity, eigenvectors, optimality of the exponent, or that the numerical runs are executions of Alg. 2 with certified comparisons (2181–2186, 2253–2258).

Theorem 1.1 is exactly the catalogue statement.

## 2. Mathematics

- **Remark 1.1 (421–432), gauge:** OK.
- **Lemma 2.1 (527–570):** coefficient count, Ky Fan with rearrangement, and Weyl slope bounds all OK. (2.2), (2.6) and (2.8) OK.
- **Lemma 3.1 (919–1170):**
  - Step 1: the discarded rows have total $`< 1/4`$, the weighted average is ≥ 3/8, q ≠ p, and $`\lVert\Pi_p - \Pi_q\rVert \ge \sqrt{3/8} > 1/2`$. OK.
  - Step 2: $`W_{i-1} - W_i = (\lambda-\mu)(u_1)_i(u_2)_i`$ with $`W_0 = 0`$ gives (3.3). OK.
  - Step 3: τ² = 16nγ ≤ 1/(16n), so $`r_p`$ and $`r_q`$ are large. Case (b) is used only on [p, q−1], consistent with $`p \le k < q`$. In case (c), $`\beta_i\det(r_{i-1}, r_{i+1}) = \det(r_{i-1}, r_i D) - (d_i - m)\det(r_{i-1}, r_i)`$, with bounds 2γ/τ² + γ/2 ≤ 5γ/τ². The path has ≤ n−1 steps, so the total is $`< 5/16 < 1/2`$. OK.
  - Step 4: $`[H, P_L] = \beta_k(e_{k+1}e_k^{\top} - e_k e_{k+1}^{\top})`$ and $`2\sqrt n(\gamma/2 + \sqrt2\tau) \le 16n\sqrt\gamma`$; same for $`v_2`$ with $`q \ge k+1`$. OK.
  - Edge cases λ = μ, n = 2 and $`\beta_i = 0`$ are covered.
- **Lemma 3.2 (1267–1344):** AQ + QA − QAQ gives $`\le 96n\sqrt\gamma`$. $`G_+ - G_- = v_2v_2^{\top} - v_1v_1^{\top}`$ gives $`S^{\mathrm{aux}} \ge 1`$. OK.
- **Prop. 3.1 (1346–1376):** $`\lvert F - F^{\mathrm{aux}}\rvert \le n\lVert\cdot\rVert_*`$, 384/1024 = 3/8, so S ≥ 5/8. It uses only ‖H‖ ≤ 2 and $`\lvert\beta\rvert \le 1`$. Tridiagonality is essential: a 3×3 non-tridiagonal T makes it fail.
- **Lemma 4.1:** child tents are ≤ (4/3) × the parent tent (sharp); errors 1/64 + 1/32. OK.
- **Thm 4.1 / Alg. 1:** $`(n^3 - n)/2 < n^3`$, $`5/32 + 2/64 < 1/2`$, 5 evaluations per refinement, $`h < 1`$. Remark 4.1 OK.
- **Lemma 4.2:** three secant comparisons and telescoping give factor 1/2 (attained). The hypothesis θ ≤ 1/4 is stronger than needed; harmless.
- **Thm 4.2 / Alg. 2:** $`2^{-K}n^3 + 1/16 < 1/8`$ and (4.4) gives $`S \le S^{(\theta)}`$. The stop-test error θ/32 ≤ 1/128 is below the margin 1/64, so the test is sound. Containment in [0, δ/n] OK. Radius: $`(1/2 - \theta)^K \ge 2^{-K-1}`$ and $`2^K < 32n^3`$ give $`h > \delta/(128n^4)`$. Evaluations: 7 + 1 per refinement, 3 + 8K in total. The tie rule is deterministic. No statement after the loop (unreachable; correction 5).
- **Lemma 4.3 / App. A:** the $`\lvert\beta\rvert^2`$ recurrence is correct; the new P₁ form is correct. Product tree O(n log² n). Graeffe G(P)(x²) = P(ix)P(−ix). The (A.1) bracket follows from C(n,j) ≤ 2^n terms and needs no simplicity assumption. $`\lvert\hat r - r\rvert \le 4n/R \le \eta/2`$; the lower side is trivial but not stated. The F error is ε/2. k = O(1 + log(n/ε)) because n/η ≤ (n/ε)³. Per-call cost O(n[1+log(n/ε)]²). OK.
- **Proof of Thm 1.1:** ≤ 3 + 8K calls with $`\varepsilon \in [\varepsilon_{\min}, 1)`$, $`\varepsilon_{\min} > \delta/(2^{16}Kn^4)`$, total O(n[1+log(n/δ)]³). OK.
- **Precision edits listed in the change record:** all re-derived and correct.
- **Sobczyk remark (2033–2053):** non-load-bearing alternative; v2 does contain an eigenvalues-only tridiagonal result (App. C.2).

## 3. Independent computation

**`check_exact.py`** (the referee's own script; standard library, Fractions; output identical under `-O`; 55 checks pass, 7/7 negative controls rejected):
- Constants for 2 ≤ n ≤ 3000, plus exact Bernoulli, radius and $`\varepsilon_{\min}`$ for n ≤ 400. K values 7, 21, 24, 27, 31.
- Tent inequality exact and sharp. Negative control: factor 1.3 rejected.
- Lemmas 4.1/4.2 and (4.4) on 3000 random convex piecewise-linear F. Factor 1/2 attained. Negative control: factor 0.45 rejected. (4.5) holds under adversarial errors.
- Examples 2.2 and 4.1 hold exactly.
- App. A, exact (n = 2..4, R up to 4096, including reducible and n-fold cases): the $`\lvert\beta\rvert^2`$ recurrence equals the full complex determinant (negative control: β² without conjugation rejected); the Graeffe identity holds (negative control: wrong sign rejected); (A.1) holds and $`\lvert\hat r - r\rvert \le \eta/2`$, checked against rigorous Sturm enclosures (negative control: a single Graeffe step violates η/2).
- Alg. 2 end to end, with exact or rigorous oracles at the full allowed adversarial error. Cases: diagonal T with total collisions and crossings at child centres; tridiagonal T with couplings 10⁻⁶ or 0, complex couplings, δ = 0.4999; two identical blocks; a full-slope-range stress F. Every run had $`j^* \le K`$ (stress test: $`j^* = K-4`$), ≤ 3 + 8K evaluations, $`h > \delta/(128n^4)`$, rigorous $`S < 1/2`$, and $`\mathrm{gap} > h^2/(2^{20}n^4)`$.
- Negative control: $`T = \begin{pmatrix}1/4&0&-1/4\\0&0&0\\-1/4&0&1/4\end{pmatrix}`$ has gap 0, yet $`S_h(0) < 1/2`$ for every $`h < 4/63`$, so Prop. 3.1 fails without tridiagonality.

**`screen_numeric.py`** (the referee's own script; mpmath, screening only): Example 2.3: 1.85412. Example 3.1: all printed values reproduced. Lemma 3.1 on 150 random cases: a cut is always found; residual ratio ≤ 2.2e-5; response difference ≥ 1. Prop. 3.1 intermediate bound: no violations. Table 2: $`g_S`$ recomputed; $`g_{\mathrm{dir}}`$, $`j^*`$ and runtimes agree with the authors' data file (0.9349 s, so 0.93 is right).

## 4. Corrections (main.tex lines)

1. 205–207, 2106–2109, 2685–2686: "no logarithm or floor of a real input is computed" is literally wrong, since doubling computes ⌈log₂(8n/η)⌉ at counted cost. Say "no logarithm, floor or bit extraction is used as a primitive operation".
2. 2711–2712: state that coefficients reach about $`4^{nR}`$ with $`R = \Theta(n^3/\varepsilon)`$, so the oracle gives no bit-complexity bound.
3. Example 3.1, 903/906: "$`\gamma_p^{\top}/\lVert\gamma_p\rVert\,(u_1,u_2)`$" has mismatched dimensions, uses $`\gamma_p`$ before its definition, and clashes with γ = 10⁻⁵. Write $`[u_1\ u_2]\,r_p^{\top}/\lVert r_p\rVert`$; use $`r_i^{\top}`$ instead of $`\gamma_i`$ at 1174–1181 and in `matrix_with_cut.tex`.
4. 863–866: the 7th entries show 0, but `matrix_with_cut.tex` shows −1.23e-7 and 7.36e-7; make them agree.
5. Algorithms 1–2: add "not reached (Thm 4.1/4.2)" after the loop (optional).
6. 190–191: say D = tX is output (n further multiplications; optional).
7. 312–315: the "tested at order 10³ … consistently audited" claim is not in Section 5 (n ≤ 500); delete or restate.
8. 316–320: the n⁻² gap decay is not shown in Section 5; add data or delete.
9. 2259–2261: the "separate rigorous fallback implementation" claim has no reported runs; delete or qualify.
10. Process wording "original/final/completed" at 2300–2301, 2364–2365, 2376–2378, 2393, 2405, 2439–2441, 2457–2458, 2480, 2512–2513.
11. Figure texts: drop the Fig. 3 footer "Final strict-Sturm implementation"; retitle Fig. 5(a) "Strict-Sturm version…" as "Total runtime" and drop its "posted…" footer.
12. Release precondition (2188–2190, 2624–2627): these lines link the folder verification/numerics/ of the code repository. This concerned the repository contents at the time of review: at release the linked folder must be present and the repository README must give this paper's title and constants.
13. Bibliography: add the arXiv ids for [1] and [24]; protect {Anderson}, {Hermitian}, {FEAST}; add volume and pages to NakatsukasaTropp2024.
14. 2036–2039: cite the specific Sobczyk result, App. C.2 of v2 (optional).

## 5. Correction check

- Items 1–4, 7–13: applied correctly. Caveats: item 4's wording "no logarithm or floor" needs correction 1; the repository link target of item 7 concerned the repository contents at the time of review (release precondition, correction 12).
- Item 5: applied in the paper (printed title equals pdftitle); the title in the repository README concerned the repository contents at the time of review (release precondition, correction 12).
- Item 6: concerns the code repository README (outside the paper; correction 12).
- Fixes (a)–(f): all applied correctly. (a) is confirmed by the data (0.9349 s). (c) is consistent with (4.4). (f) gives the same polynomial, checked exactly.

The source-to-final diff matches the change record; there are no undocumented content changes.

## 6. Public readiness

- The AI-use declaration has the intended form; no other tool or process names appear.
- Author block, funding (EPSRC only), competing interests and the absence of a date match the authors' reference version.
- Process wording remains in §5 and two figures (corrections 7–11).
- The data pointer concerned the repository contents at the time of review (release precondition, correction 12).
- The build is clean; three uncited bib entries are harmless.

**Verdict:** (i) ACCEPT. (ii) ACCEPT WITH CORRECTIONS: corrections 1–2 are minor; 7–13 are needed before release, and 12 is a release precondition.
