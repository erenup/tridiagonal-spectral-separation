Reviewed: the final text in paper/ (main.tex and main.pdf; 28 pages), against the catalogue statement of KE-02, including a check of the corrections made since the earlier draft.

# Referee report D: "A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices" (W. Zhu, P. Nie), final text

**Verdicts:** (i) the gap theorem: **ACCEPT**. (ii) the full KE-02 target, including the operation count ($`a = 12`$, $`c_0 = 2^{-34}`$, $`q = 3`$, exact-real model): **ACCEPT**. Text for posting: **ACCEPT WITH CORRECTIONS**. No mathematical gap or error found. Every constant re-derives (16n√γ, 96n√γ, 5/8, $`2^{-20}`$, 1/64, 1/32, 1/8, δ/(128n⁴), $`2^{-34}`$) and every exact test passes.

List of corrections: items 1–4 and 8–13 and the extra fixes (a)–(f) are applied correctly in the paper. Item 5 is done in the paper; its code-repository part, item 6 (the code repository README) and the link target of item 7 concerned the repository contents at the time of review; all three point to C1.

## Files and reading order
- Reviewed `paper/main.tex` (sha256 6428c025…40ec) and `paper/main.pdf` (a8b92e60…5001, 28 pp.). The catalogue statement of KE-02 was fetched from the catalogue.
- Read before the derivation: the catalogue entry; main.tex lines 1–2719 with `matrix_with_cut.tex`, `vectors_with_cut.tex` and `refs.bib`; the PDF metadata of main.pdf.
- Opened only after the derivation and independent tests were written down (notes timestamped): the earlier 27-page draft (PDF and source), the list of corrections and the change record.

## 1. Target fidelity
- The paper matches the catalogue statement point by point: every n ≥ 2, Hermitian tridiagonal T with ‖T‖ ≤ 1, δ ∈ (0, 1/2); deterministic, and reads only $`d_i`$ and $`\lvert\beta_i\rvert^2`$; returns a real diagonal D = tX with t ∈ [0, δ/n], so ‖D‖ ≤ δ; $`\mathrm{gap}(T+D) > 2^{-34}\delta^2 n^{-12} \ge 2^{-34}(\delta/n)^{12}`$; cost O(n[1+log(n/δ)]³), using arithmetic, comparisons and square roots only.
- The gap in eq. (2) is the catalogue's quantity. C is an implicit O-constant, which the statement allows.
- The Graeffe oracle relies on unit-cost exact arithmetic on numbers of size about $`4^{nR}`$. The catalogue's model permits this, and the paper says so (l.2126–2128, 2558–2563, 2711–2712).

## 2. Mathematics (main.tex line numbers; all OK unless marked)
**Section 2.** Remark 1.1, gauge (421–432). Lemma 2.1, Ky Fan convexity, slope range [n(n+1)/2, n²(n+1)/2], variational formula (527–570). Eqs. (8) and (12) (494–497, 588–593). Definition 2.1 and eqs. (14)–(15) (621–669). Examples 2.2 and 2.3: 1.854118 reproduced.

**Lemma 3.1.** Step 1 (942–981): weighted average gives 3/8, so $`\lVert\Pi_p - \Pi_q\rVert \ge \sqrt{3/8}`$. Step 2 (983–1021): Wronskian from $`W_{i-1} - W_i = (\lambda-\mu)(u_1)_i(u_2)_i`$, giving $`\lvert\cdot\rvert \le \gamma/2`$. Step 3 (1023–1116): in case (c), $`\lvert d_i - c\rvert \le 4`$, and both cuts i−1, i lie in [p, q−1]; the bound in (c) is 2γ/τ² + γ/2 ≤ 5γ/τ²; the path has at most n−1 steps, so the total is $`< 5/16`$. Step 4 (1118–1169): commutator has two terms; residual ≤ 16n√γ.

**Lemma 3.2 and Prop. 3.1.** Lemma 3.2 (1289–1343): nuclear norm ≤ 96n√γ; maximizers G± give $`S^{\mathrm{aux}} \ge 1`$. Prop. 3.1 (1346–1376): $`S_h \ge 1 - 384/1024 = 5/8`$.

**Section 4.** Lemma 4.1 (1502–1577): 4/3 weight bound, errors 1/64 and 1/32; wording issue C8. Thm 4.1 and Remark 4.1 (1600–1702). Eq. (34) (1729–1743). Lemma 4.2 (1801–1871): each secant inclusion checked. Alg. 2 (1756–1794): stopping test is sound because $`\lvert\hat S - S\rvert \le \theta/32`$; the tie rule is deterministic. Thm 4.2 (1875–1960): stops by iteration K because the potential is $`< 1/8`$; the window stays in [0, δ/n]; $`h_K > \delta/(128n^4)`$, by Bernoulli and $`2^K < 32n^3`$; at most 3+8K evaluations. $`\varepsilon_{\min} = h/(512K)`$ (2063–2076). Lemma 4.3 (1992–2031).

**Appendix A and the main theorem.** Continuant, product tree, FFT with half-angle roots of unity (2642–2667). Graeffe G(P) = E(−z)² + zO(−z)², $`p_j \le e_j \le 2^n p_j`$ (2669–2682). Doubling for k; $`\lvert\hat r - r\rvert \le 4n/R \le \eta/2`$; index-wise matching (2683–2712). Proof of Thm 1.1 (2083–2110). Examples 3.1 and 3.2: data reproduced; minor notation issues C2–C4.

**Edge cases.** n = 2 works: the only cut is k = 1. Repeated eigenvalues are allowed in Lemma 3.1 and are safe in the Graeffe bound. A zero β gives zero leakage at that cut. Complex β enters only through $`\lvert\beta\rvert^2`$. For δ near 1/2, $`\lVert H(t)\rVert < 3/2`$.

## 3. Independent computation
The scripts named below are the referee's own. Exact scripts use the standard library (Fractions) and fail closed; their output is byte-identical under `python -I -O`.
- `run_selectors.py`: 480 exact runs pass. Algorithms 1 and 2 ran with an exact Sturm oracle and three admissible error modes (exact, random, hostile). Inputs: n = 2–7; zero, Toeplitz, Wilkinson and complex-modulus matrices; zero-edge blocks; random; dense crossings; δ = 0.3 and 0.4999; a "full collision" case where all n eigenvalues coincide at the starting centre. Each run certifies the K bound, the 3+8K count, the window, the h bound, the recursion at every step, $`S < 1/2`$, and both gap bounds.
- `test_long_runs.py`: exact diagonal spread-crossing families up to n = 100; convex functions using the full slope budget (the quadratic case needs K−5 refinements at n = 10, 100, 1000); unreduced tridiagonals with n = 8, 12. Negative control: with stopping threshold $`2^{-12}`$ the K bound breaks, as expected.
- `test_oracle.py`: 14 exact checks pass (complex determinant equals the continuant with $`\lvert\beta\rvert^2`$, and the product tree agrees; the Graeffe identity holds; (43) and the η/2 error bound hold against Sturm enclosures; $`\lvert\hat F - F\rvert \le \varepsilon`$). Negative controls (wrong Graeffe sign, perturbed coefficient, R = 1, β² instead of $`\lvert\beta\rvert^2`$) are all rejected.
- `test_contraction.py`: 3000 random piecewise-linear convex functions; the factors 2/3 and 1/2 are attained exactly; 0.65 and 0.49 are rejected.
- `test_localization.py` (mpmath screen, 60 digits): Lemma 3.1 checked for every admissible (p, q, k) on Wilkinson W11+ and W21+, weak-edge blocks, Example 3.1 and random cases; largest residual 0.06 × 16n√γ. Lemma 3.2 and Prop. 3.1 hold on the same cases. Non-tridiagonal negative control: gap 0 but $`S_{0.01}(0) = 0.28 < 1/2`$, so the tridiagonal order is necessary. All seven Table 2 $`g_S`$ values match.
- `test_negative_checker.py`: outputs produced from an oracle that violates the tolerance are rejected (3 of 3).
- Build and references: a fresh build gives text identical to main.pdf, with no undefined references or overfull boxes. All DOIs and both arXiv IDs resolve to the cited works.

## 4. Corrections (main.tex line numbers)
- C1 (release precondition). l.2188–2190 and l.2624–2627 link the repository folder `verification/numerics/`. This concerned the repository contents at the time of review: at release the repository must contain the Section 5 code and data and give this paper's title and constants ($`a = 12`$, $`c_0 = 2^{-34}`$), or the link must change.
- C2. l.903 and l.906: "$`(\gamma_p^T/\lVert\gamma_p\rVert)(u_1,u_2)`$" multiplies 1×2 by n×2, uses $`\gamma_p`$ before it is defined (l.1176), and clashes with $`\gamma = 10^{-5}`$. Use "$`(u_1,u_2)\,r_p^T/\lVert r_p\rVert_2`$".
- C3. l.863–866 print the 7th entries of u1, u2 as 0; `matrix_with_cut.tex` shows −1.23e-7 and 7.36e-7. Use the same values in both.
- C4. l.1175–1185 name the columns $`\gamma_i`$ while $`\gamma = 10^{-5}`$ in l.1181. Rename the columns.
- C5. l.312–315 say the code was "tested at dimensions of order 10^3", with "consistently audited" benchmarks. No such run is reported (largest n = 500). Rephrase or delete.
- C6. l.2259–2261 cite "A separate rigorous fallback implementation", which is neither described nor linked. Delete, or describe and link it.
- C7. Process-history wording at l.2376–2378, 2440–2441, 2457–2458, 2479–2480 and 2512–2513 ("the original …"). Replace with neutral descriptions.
- C8. l.1520–1522, "after j iterations" → "for every refinement j that is performed".
- C9. refs.bib, NakatsukasaTropp2024: add volume 45, pages 1183–1214.
- C10 (optional). In App. A (l.2711–2712), note that the coefficients grow to about $`4^{nR}`$ with $`R = \Theta(n^3/\varepsilon)`$. In Alg. 1 (l.1441), say $`K_b`$ is found by repeated multiplication and comparison, as Alg. 2 does for K.

## 5. Correction check
The diff between the source of the earlier draft and the final source contains only the hunks listed in the change record; no unlisted mathematical change.

| Item (list of corrections) | Status | Final location (main.tex) |
|---|---|---|
| 1 Explicit constant | applied correctly | l.57, l.288, l.196–197 |
| 2 Conditional wording removed | applied correctly | l.64–67, l.2533–2537 |
| 3 Main theorem, q = 3 | applied correctly | Thm 1.1 l.185–209; l.133/135, 2003, 2081 |
| 4 Doubling, pairs, $`\lvert\beta\rvert^2`$, labels | applied correctly | l.1764–1766; l.2644–2706 |
| 5 One title | paper done (l.16 = l.35); code repository → C1 | |
| 6 Code README constant | outside the paper → C1 | |
| 7 Numerics relabelled | text done; link target → C1 | |
| 8 Lemma 3.1 precision | applied correctly | l.951–963, 1094–1097, 1099–1114 |
| 9 Lemma 3.2 norms | applied correctly | l.1302–1325 |
| 10 Lemma 4.2 secant chain | applied correctly | l.1830–1861 |
| 11 Thm 4.2 window, shared point | applied correctly | l.1884, 1924–1929, 1950–1959 |
| 12 Lemma 4.3 cost inline | applied correctly | l.2008–2030 |
| 13 Declarations | applied correctly (link → C1) | l.36–44, 2615–2636 |
| (a) 0.93 s | applied | l.2390, 2428 |
| (b) pdftitle | applied correctly | l.16 |
| (c) θ ≤ 1/2 | applied correctly | l.1715 |
| (d) $`h < 1`$ in Thm 4.2 | applied correctly | l.1944 |
| (e) $`h < 1`$ in Thm 4.1 | applied correctly | l.1682–1683 |
| (f) App. A recurrence | applied correctly | l.2654–2656 |

## 6. Public readiness
The main theorem comes first, the proofs are complete, and only $`2^{-34}`$ appears. Process history and unsupported claims remain only in the numerics section (C5–C7). The code and data link is a release precondition (C1). The single AI declaration is at l.2629–2636. The build is clean, and one bibliography entry is incomplete (C9).
