Reviewed: an earlier 27-page draft of the paper, against the catalogue statement of KE-02.

# Referee report A: earlier draft of the paper

## Verdicts

- (i) Gap theorem (Thm 4.2: $`\mathrm{gap} > 2^{-34}\delta^2 n^{-12}`$, at most $`K = \lceil\log_2(16n^3)\rceil`$
  refinements, $`h > \delta/(128n^4)`$): ACCEPT WITH CORRECTIONS — every step checks out, no counterexample.
- (ii) Full KE-02 target including complexity: ACCEPT WITH CORRECTIONS (C1–C4 mandatory). The spectral-function oracle
  is CONSTRUCTED (Lemma 4.3 + Appendix A: continuant recurrence, balanced product tree with FFT via half-angle square
  roots, Graeffe squaring, coefficient ratios with R-th roots by repeated square roots) — essentially the construction
  of an earlier version of the argument. Defects are in the statement: abstract (l.89–90) and conclusion (l.2409) make
  the cost sound conditional; no theorem states operation count and model ($`q=4`$ only in prose, §4.3); choice of k
  without bit extraction unstated.

Against the target: $`\mathrm{gap} > 2^{-34}\delta^2 n^{-12} \ge 2^{-34}(\delta/n)^{12}`$ ⇒ $`a=12`$,
$`c_0=2^{-34}`$, $`q=4`$ (per-call $`O(n[1+\log(n/\varepsilon)]^2)`$ ⇒ $`q=3`$ also holds).

## Step table

- Rem 1.1 real reduction: OK.
- Lem 2.1 convexity/slopes/variational formula: OK ($`S \le (n^3-n)/2 < n^3`$).
- §2 spread identity, integral form of $`S_h`$, Ex 2.2/2.3: OK (1.85412 reproduced).
- Lem 3.1 localization: OK (Wronskian, $`\tau \le 1/(4\sqrt n)`$, cases (a)–(c), $`5/16 < 1/2`$, residual
  $`\le 16n\sqrt{\gamma}`$, X-response $`\ge 1`$; $`n=2`$ forces $`k=1`$; $`\beta_k=0`$ is a cut; $`\lambda=\mu`$
  allowed).
- Lem 3.2 auxiliary matrix: OK ($`3\sqrt2\cdot\sqrt2\cdot16 = 96`$; $`S^{\mathrm{aux}} \ge 1`$).
- Prop 3.1 local gap certificate: OK ($`384/1024 = 3/8`$, $`S \ge 5/8 > 1/2`$; $`\lVert H\rVert < 3/2`$,
  $`\lvert d_i - c\rvert \le 4`$, $`\lvert\beta\rvert \le 1`$, fine for δ near 1/2).
- Lem 4.1 triangular-weight contraction: OK (2/3 sharp; slack 1/32).
- Thm 4.1/Rem 4.1 basic selector: OK ($`1/16+3/32+2/64 < 1/2`$; $`3+5K_b`$ evaluations).
- Eq. 25, $`S_h \le S^{(\theta)}`$: OK for $`\theta \le 1/2`$.
- Lem 4.2 endpoint contraction: OK, terse (C7).
- Thm 4.2 improved selector: OK (bound $`< 1/8`$; error $`\theta/32 \le 1/128`$; $`2^K < 32n^3`$;
  $`128^2\cdot2^{20} = 2^{34}`$; "$`\le 8`$ evaluations" needs the shared point evaluated once).
- Lem 4.3/App A oracle: OK, terse (Graeffe identity, $`p_j \le e_j \le 2^n p_j`$,
  $`\lvert\hat r - r\rvert \le 4n/R \le \eta/2`$, $`\varepsilon_{\min} > \delta/(2^{16}Kn^4)`$).
- §4.3 total cost: OK, informal (not a theorem; model not stated).
- §5 numerics: illustration only (double-precision selection path, not Algorithm 2's error-controlled comparisons).

## Corrections

- C1 abstract l.80–90: "$`c>0`$ is a constant" → "$`c=2^{-34}`$"; replace "Coupled with a suitable spectral-function
  oracle..." by a direct statement: an exact-arithmetic oracle (Appendix A) gives $`O(n[1+\log(n/\delta)]^4)`$
  arithmetic operations, comparisons and square roots in total.
- C2 l.2408–09: delete "subject to the stated spectral-oracle model".
- C3 new main theorem (§1 or end of §4.3): gap, budget, operation count and the catalogue model together (exact real
  operations and comparisons, unit-cost square roots of nonnegative reals, no bit extraction); state
  $`\mathrm{gap} \ge 2^{-34}(\delta/n)^{12}`$; eq. (3) l.154 rename exponent p → a; eq. (6) l.279
  "$`\ge c\,\delta^2/n^{12}`$" → "$`> 2^{-34}\delta^2/n^{12}`$".
- C4 App A l.2551; Alg 2 l.1746: K and k (least k with $`2^k \ge 8n/\eta`$) found by doubling and comparisons, no
  log/floor of a real input.
- C5 l.2555–56: "reverse the approximate $`r_j`$ into nondecreasing order" → "set
  $`\hat\lambda_j = \hat r_{n+1-j} - 2`$".
- C6 Lem 4.3 proof l.1942: inline cost accounting $`O(n[1+\log(n/\varepsilon)]^2)`$ per call (⇒ $`q=3`$).
- C7 Lem 4.2 proof l.1806–15: write out the secant chain.
- C8 Lem 3.1 minor: case (c) state $`\gamma/2 \le 3\gamma/\tau^2`$ since $`\tau^2 \le 1/(16n)`$; Step 1 state the
  weighted-average argument giving q.
- C9 title l.15 vs l.35/PDF metadata/file name — unify.
- C10 code repository README: its constant concerned the repository contents at the time of review (release
  precondition); align it with $`2^{-34}`$.
- C11 §5 l.2063–2137: label explicitly as illustration; certification code "on request" only.
- C12 l.2501: the AI declaration names vendors (its form is the authors' decision).

## Independent tests

Exact Fractions / mpmath 80 digits.

- All constants for n = 2..299, 1e3, 12345, 1e5, 1e6.
- Lemmas 4.1, 4.2 and $`S \le S^{(\theta)}`$ on 4000 random convex PL functions (2/3 attained).
- Lemma 3.1 literally, Lemma 3.2, Prop 3.1 contrapositive on Wilkinson, twin blocks with complex edges coupled at
  1e-12..1e-30, exact crossings with zero or 1e-25 edges at δ = 0.4999 incl. n = 2, equal blocks with gap 0 — all pass
  ($`S_h \ge 1`$ observed).
- 1920 exact runs of Algorithms 1 and 2 (n = 2..16, four deltas, three adversarial oracle-error modes): stop within K,
  $`h > \delta/(128n^4)`$, true $`S_h < 1/2`$, $`\mathrm{gap} > h^2/(2^{20}n^4)`$ and
  $`> 2^{-34}\delta^2n^{-12}`$.
- Uniform maximal curvature gives stopping radius ≈ 0.68–0.86 $`\delta/n^4`$ ($`n^{-4}`$ radius, hence $`n^{-12}`$, is
  the method's limit).
- Continuant + 10 Graeffe steps exact, $`Q(w)Q(-w) = G(-w^2)`$, ratio bounds and
  $`\lvert\hat\lambda - \lambda\rvert \le \eta/2`$, $`\lvert\hat F - F\rvert \le \varepsilon`$ vs 60-digit eigenvalues,
  n = 2..6.
- Example 3.1 and Table 2 reproduced.
