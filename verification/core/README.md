# Exact checks of the constants and of the Appendix A algebra

This folder contains exact, standard-library-only checks for the paper

> **A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices**

whose main theorem gives, for Hermitian tridiagonal $`T`$ with $`\lVert T\rVert_2\le 1`$, $`n\ge 2`$ and
$`0<\delta<1/2`$, a parameter $`t\in[0,\delta/n]`$ with

```math
\lVert tX\rVert_2\le\delta,\qquad \mathrm{gap}(T+tX)>2^{-34}\,\delta^2 n^{-12},\qquad X=\mathrm{diag}(1,\dots,n).
```

The checks transcribe every numerical constant and inequality chain of the proofs in Sections 2–4
(Lemma 2.1 through Theorem 4.2 and Lemma 4.3) and the algebra of Appendix A, and verify them with exact
integer and rational arithmetic.

**What these checks are, and what they are not.** They are *finite exact cross-checks*. A statement of
the paper that is universal in $`n`$ or $`K`$ is checked exactly on the finite range printed in the
output (for example $`2\le n\le 10^4`$, $`1\le K\le 1024`$); a statement about all matrices, all convex
functions or all real parameters is checked exactly on fixed instances. Such checks can detect a wrong
constant, a wrong sign or a wrong index, but they do not prove the universal statements. Those are
proved in the paper; the finite and scalar core is in addition proved universally in the accompanying
Lean formalization, whose `SCOPE.md` lists exactly what it covers. The checks here are independent of
the Lean proofs and are not a substitute for them. The one complete finite verification is the weight
inequality in the proof of Lemma 4.1: in the variable $`(x-t)/h`$ both sides are piecewise linear with
known breakpoints, so checking the breakpoints covers all real $`x`$ (C09); the general case is the
affine change of variable.

Equation numbers refer to [paper/main.pdf](../../paper/main.pdf): the bound of Remark 4.1 is (32), the output
of Theorem 4.2 is (37), the smallest oracle accuracy is (40), and the Graeffe ratio bound of
Appendix A is (43).

## How to run

Python 3.11 or later, standard library only; no network access, and no file is written.

```sh
python3 -S -s -B run_checks.py
python3 -S -s -B -O run_checks.py
```

Expected final line of both commands (exit status 0):

```text
RESULT: PASS KE-02 exact checks
```

`run_checks.py` verifies [SHA256SUMS](SHA256SUMS), lints the sources, and runs each checker five times:
in-process, and as subprocesses under `python3 -S -s -B` and `python3 -S -s -B -O`, each with
`PYTHONHASHSEED=0` and `PYTHONHASHSEED=1`. It requires exit status 0, empty standard error and
byte-identical standard output in all five runs, the pinned numbers of checks and negative controls,
and that [CHECKERS.txt](CHECKERS.txt) lists exactly the negative controls that were executed. The
checkers can also be run on their own:

```sh
python3 -S -s -B check_constants.py      # final line: RESULT: PASS check_constants.py: 208690 checks, 43 negative controls rejected
python3 -S -s -B check_appendix_a.py     # final line: RESULT: PASS check_appendix_a.py: 2660 checks, 13 negative controls rejected
```

The whole run takes well under a minute.

## Exactness and determinism

* Every decision compares Python integers or `fractions.Fraction` values; the comparison helpers reject
  any other type at run time, and the lint step rejects float and complex literals, `float()`,
  `complex()`, `pow()`, `assert` (which `-O` removes) and integer powers with negative literal exponents.
* Square roots enter only through rational brackets $`\ell\le\sqrt x<u`$, verified by exact squaring.
  The $`R`$-th roots of Appendix A, $`R=2^k`$, are bracketed by $`k`$ successive square roots, each
  verified by exact squaring.
* Eigenvalues of rational tridiagonal matrices with irrational spectra enter only through exact Sturm
  bisection: the number of eigenvalues below a rational $`x`$ is the number of negative pivots of the
  exact $`LDL^{\mathsf T}`$ factorization of $`A-xI`$ (Sylvester's law of inertia).
* Symbolic reductions (powers of $`n,\delta,h,\gamma,K`$ and constants such as $`\sqrt2`$) are checked by
  a small exact monomial calculus with rational exponents.
* All test data come from a fixed SHA-256 counter-mode generator, so they do not depend on the `random`
  module, the Python version or `PYTHONHASHSEED`.
* Every failure prints a line beginning with `FAIL:` and gives a nonzero exit status; an exception, a
  family without checks, or a family without rejected negative controls is a failure.

## The checks

### `check_constants.py`

| Family | Paper | What is checked exactly |
|---|---|---|
| C01 | Lemma 2.1, (8)–(10); proofs of Theorems 4.1, 4.2 | $`\sum_j j=n(n+1)/2`$, $`\sum_j jn=n^2(n+1)/2`$; the slope width $`(n^3-n)/2<n^3`$ for $`n\le10^4`$; (8) and (10) on exact sorted spectra; (9), convexity and $`0\le\mathcal S_h(t)\le(n^3-n)/2`$ for exact diagonal $`T`$ |
| C02 | Examples 2.2, 2.3, 3.1, 3.2, 4.1 | (16), (17) and Example 4.1 exactly; the crossings $`0.06,0.08,0.10`$; $`\mathcal S_{0.006}(0.08)\in[1.854117,1.854118]`$, which rounds to the stated $`1.8541`$; for Example 3.1, $`\lVert H\rVert_2<1`$, the two eigenvalues $`-5.173792\times10^{-6}`$ and $`4.739763\times10^{-6}`$ to $`10^{-12}`$, $`\lvert\lambda-\mu\rvert<\gamma`$; $`\tau\approx0.0358`$ and the column $`L_k\le\tau`$ of the table in Example 3.2 |
| C03 | Lemma 3.1, Step 1, (21) | $`n(1/(2\sqrt n))^2=1/4`$, $`3/4`$, $`(3/4)/2=3/8`$, $`\sqrt{3/8}>1/2`$; $`\lVert \Pi_a-\Pi_b\rVert_2^2=\det(a,b)^2/(\lvert a\rvert^2\lvert b\rvert^2)`$; the whole of Step 1 on exact $`n\times2`$ matrices with orthonormal rational columns (Cayley transforms) |
| C04 | Lemma 3.1, Step 2, (22) | the discrete Wronskian identity in telescoping form for arbitrary vectors, and for exact eigenpairs; $`\lvert\sum_{j\le i}(u_1)_j(u_2)_j\rvert\le1/2`$ for orthonormal rational pairs |
| C05 | Lemma 3.1, Step 3, (23) | $`\tau^2=16n\gamma`$, $`\tau\le1/(4\sqrt n)`$, cases (a) and (c) (including the determinant step from the three-term recurrence), $`5\gamma/\tau^2=5/(16n)`$, $`(n-1)\cdot5/(16n)<5/16<1/2`$ for $`n\le10^4`$ |
| C06 | Lemma 3.1, Step 4, (20) | the residual $`\lvert\lambda-\mu\rvert/2`$ of $`w_1`$; the commutator $`[H,P_L]w`$ and its bound $`\sqrt2\tau`$; $`2\sqrt n(\gamma/2+\sqrt2\tau)\le4\sqrt n\tau=16n\sqrt\gamma`$; the $`X`$-responses $`\le k`$ and $`\ge k+1`$ |
| C07 | Lemma 3.2, (26), (27) | $`H-\widetilde H=AQ+QA-QAQ`$, $`\widetilde Hv_i=\tfrac{\lambda+\mu}2v_i`$, $`\lVert AQ\rVert_{\mathrm F}^2=\sum_i\lVert Av_i\rVert^2`$, rank $`\le2`$ and $`\lVert M\rVert_*\le\sqrt2\lVert M\rVert_{\mathrm F}`$ on exact instances; $`3\sqrt2\cdot\sqrt2\cdot16=96`$; (27) for exact diagonal $`\widetilde H`$ with a repeated eigenvalue |
| C08 | Proposition 3.1, (19), (28) | $`0<h\le1\Rightarrow\gamma=h^2/(2^{20}n^4)\le1/(256n^2)`$; the transfer coefficient $`1+2+1=4`$; $`(4n/h)\cdot96n\sqrt\gamma=384/1024=3/8`$ and $`1-3/8=5/8>1/2`$ (symbolically, for $`n\le10^4`$ at $`h=1`$, and on 2000 sampled complete chains); (28) on exact diagonal pairs |
| C09 | Lemma 4.1, (29), (30) | the weight inequality $`w_{t-h/4,h/4}+w_{t+h/4,h/4}\le\tfrac43w_{t,h}`$ and its extremal value $`4/3`$ at $`x=t\mp h/4`$; the representation $`\mathcal S_h(t)=\int w_{t,h}\,d\nu`$, (29) and its sharpness, and (30) with replies within $`r/256`$ on random convex piecewise-linear $`F`$ |
| C10 | Theorem 4.1, Remark 4.1, (31), (32) | $`K_{\mathrm b}`$ least with $`(3/2)^{K_{\mathrm b}}\ge16n^3`$ (two methods), $`(2/3)^{K_{\mathrm b}}n^3\le1/16`$ and $`s_{K_{\mathrm b}}<5/32`$ for $`n\le10^4`$; the iteration closed form; $`5/32+2/64<1/2`$; (31); (32) reduced to $`(3/2)^{K_{\mathrm b}-1}<16n^3`$; five evaluations per refinement |
| C11 | Lemma 4.2, (33)–(36) | (34) for $`0<\theta\le1/2`$, (35) and the three secant orderings of its proof for $`0<\theta\le1/4`$, sharpness of $`1/2`$, the error $`1/64`$ from the tolerance $`2\theta h'/256`$, and (36), on random convex piecewise-linear $`F`$ |
| C12 | Algorithm 2, Theorem 4.2, (37)–(40), Theorem 1.1, (5) | for $`2\le n\le10^4`$: $`K`$ by doubling equals the least $`K`$ with $`2^K\ge16n^3`$ and $`\lceil\log_2(16n^3)\rceil`$, $`2^K<32n^3`$, $`\theta=1/(4K)\le1/28`$, $`2^{-K}n^3+\tfrac1{32}\sum_j2^{-j}<1/8`$, $`\theta/32\le1/128`$, $`1/8+1/128+1/64<1/2`$, $`(1/2-\theta)^K>1/(64n^3)`$ (that is, $`L_K>\delta/(64n^4)`$), $`h>\delta/(128n^4)`$, (40), eight evaluations per refinement; $`(1-1/(2K))^K\ge1/2`$ for $`K\le1024`$; the symbolic reduction of $`h^2/(2^{20}n^4)>2^{-34}\delta^2n^{-12}`$ ($`128^2\cdot2^{20}=2^{34}`$) and sampled instances; (5) |
| C13 | Algorithms 1 and 2, Theorems 4.1 and 4.2 | both algorithms run as transcripts on exact instances (diagonal $`T`$, for which the gap is computed exactly, and convex piecewise-linear $`F`$ satisfying (9), including adversarial kink trees that force up to 8 refinements), with exact replies and replies within the tolerances: termination within $`K`$ (resp. $`K_{\mathrm b}`$) refinements, $`3+8j`$ (resp. $`3+5j`$) requests, nesting in $`[0,\delta/n]`$, (36) (resp. (30)) along the run, (37) (resp. (31)), (40), and $`\mathrm{gap}(T+tX)>h^2/(2^{20}n^4)>2^{-34}\delta^2n^{-12}`$ for diagonal $`T`$ |
| C14 | Lemma 4.3, Section 4.3, Appendix A | $`\eta=\varepsilon/\sum_jj=2\varepsilon/(n(n+1))`$, $`n/\eta\le(n/\varepsilon)^3`$, $`R=2^k`$ by doubling with $`8n/\eta\le R<16n/\eta`$, $`n\le R`$, $`4n/R\le\eta/2`$; $`2^x-1\le x`$ and $`1-2^{-x}\le x`$ at all $`x=p/q\in[0,1]`$ with $`q\le40`$; $`rn/R<4n/R`$ for $`0<r<4`$; total error $`\sum_jj\,\eta/2=\varepsilon/2\le\varepsilon`$ |

### `check_appendix_a.py`

| Family | Paper | What is checked exactly |
|---|---|---|
| A01 | Appendix A, the recurrence | $`P_0=1`$, $`P_1=z+2+a_1`$, $`P_i=(z+2+a_i)P_{i-1}-c_{i-1}P_{i-2}`$ equals $`\det(zI+2I+A)`$ as an exact polynomial, with the determinant computed independently by rational Gaussian elimination at $`n+1`$ points and interpolation (two further points checked), and for $`n\le7`$ also by the permutation expansion; 48 real symmetric instances ($`n=1,\dots,8`$), 32 complex Hermitian instances with $`c_i=(\mathrm{Re}\,A_{i,i+1})^2+(\mathrm{Im}\,A_{i,i+1})^2`$ (the determinant is real), and scaled Kac matrices |
| A02 | Appendix A, Graeffe | $`P(z)=E(z^2)+zO(z^2)`$; $`G(P)(z)=E(-z)^2+zO(-z)^2=\prod_j(z+r_j^2)`$ and $`k`$ steps give $`\prod_j(z+r_j^{2^k})`$, monic, for random rational roots with mixed signs, zeros and ties; the coefficient of $`z^{n-j}`$ is $`e_j`$ |
| A03 | Appendix A, (43) | for $`r_1\ge\dots\ge r_n>0`$ (with ties) and $`R=2^k`$, $`k\le6`$: $`e_0=1`$, $`e_j>0`$, $`p_j\le e_j\le\binom nj p_j\le2^np_j`$, and (43) in $`R`$-th-power form $`r_j^R2^{-n}\le e_j/e_{j-1}\le r_j^R2^n`$ |
| A04 | Appendix A, Lemma 4.3 | the complete pipeline: Gershgorin $`\lVert A\rVert_2<2`$; the integer-scaled recurrence; $`P(z)=\prod_j(z+r_j)`$ with $`r_j=2+\lambda_{n+1-j}`$ where the spectrum is known; $`\eta`$, $`R`$ by doubling, $`k`$ Graeffe steps, $`(e_j/e_{j-1})^{1/R}`$ by $`k`$ verified square roots, (43), $`\lvert\widehat r_j-r_j\rvert\le4n/R`$, the index-wise matching $`\widehat\lambda_j=\widehat r_{n+1-j}-2`$ with $`\lvert\widehat\lambda_j-\lambda_j\rvert\le\eta/2`$, and the weighted error $`\le\varepsilon`$; on scaled Clement matrices (spectrum $`(2k-n+1)/n`$), Pythagorean $`2\times2`$ blocks and diagonal matrices with repeated eigenvalues, and generic rational matrices with exact Sturm brackets; $`R`$ up to $`2^{13}`$ |

### Negative controls

Every family runs negative controls: deliberately wrong constants, formulas or inputs, each of which
must be rejected (for example $`2^{18}`$ instead of $`2^{20}`$, the constant $`192`$ instead of $`96`$,
the weight constant $`5/4`$ instead of $`4/3`$, $`\theta=1/(2K)`$, the bound
$`h^2/(2^{20}n^4)>2^{-34}\delta^2n^{-12}`$ with its constant doubled, which fails just above the minimal
radius, the Graeffe transform with the wrong sign, $`c_i=\beta_i`$ instead of
$`\lvert\beta_i\rvert^2`$, the matching $`\widehat\lambda_j=\widehat r_j-2`$ without index reversal).
[CHECKERS.txt](CHECKERS.txt) lists all 70 controls: 43 in `check_constants.py`, 13 in
`check_appendix_a.py` and 14 in `run_checks.py`. The controls of `run_checks.py` corrupt one byte of an
output, modify a file and add an unlisted file in memory, run a subprocess that fails, feed forbidden
constructs to the lint step, and run each checker with `--inject-fault`, which replaces one constant of
a positive check by a wrong one and must make the checker fail.

## Scope

Not checked here: the spectral theory behind Lemma 2.1 and (11)–(15), the existence statements of
Lemmas 3.1 and 3.2 for general matrices, operator–nuclear duality, the cost and complexity bounds, and
the numerical experiments of Section 5. Where the checks touch these statements they do so only on exact
instances, as described in the tables.

## Files

| File | Content |
|---|---|
| `check_constants.py` | families C01–C14 |
| `check_appendix_a.py` | families A01–A04 |
| `run_checks.py` | the runner described above |
| `CHECKERS.txt` | the checkers and their negative controls |
| `SHA256SUMS` | SHA-256 of every other file of this folder (`sha256sum -c SHA256SUMS`) |
