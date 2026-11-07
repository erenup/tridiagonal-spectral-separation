# A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices

Authors: Wenqi Zhu; Ping Nie.

Wenqi Zhu — Mathematical Institute, Woodstock Road, University of Oxford, Oxford, UK, OX2 6GG — wenqi.zhu@maths.ox.ac.uk

Ping Nie — David R. Cheriton School of Computer Science, University of Waterloo — ping.nie@uwaterloo.ca

Read the [paper](paper/main.pdf) and its [LaTeX source](paper/main.tex).
The main theorem answers the
[catalogue question KE-02](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/3017ea813328900a812c0c105ca16ad6f694857e/eigenvalues-and-inverse-problems/KE-02/README.md),
which asks for a nearly linear deterministic construction of a small
diagonal perturbation that separates the eigenvalues of every normalized
Hermitian tridiagonal matrix.

## Main theorem

For a Hermitian matrix $T\in\mathbb C^{n\times n}$ with eigenvalues
$`\lambda_1(T)\leq\cdots\leq\lambda_n(T)`$, listed with multiplicity, the
paper writes

```math
\mathrm{gap}(T)=\min_{1\leq j<n}\bigl(\lambda_{j+1}(T)-\lambda_j(T)\bigr),
\qquad
X=\mathrm{diag}(1,\ldots,n).
```

**Theorem 1.1 (Main theorem).** Let $n\geq2$, $`0<\delta<1/2`$, and let
$T\in\mathbb C^{n\times n}$ be Hermitian tridiagonal with
$`\lVert T\rVert_2\leq1`$. The deterministic Algorithm 2, with the
spectral-function oracle of Lemma 4.3, computes $`t\in[0,\delta/n]`$ and
outputs the real diagonal matrix $D=tX$, using $n$ further multiplications;
this matrix satisfies

```math
\lVert D\rVert_2\leq\delta,
\qquad
\mathrm{gap}(T+D)>2^{-34}\frac{\delta^2}{n^{12}}
\geq2^{-34}\Bigl(\frac{\delta}{n}\Bigr)^{12}.
```

It uses $`O\bigl(n[1+\log(n/\delta)]^3\bigr)`$ arithmetic operations,
comparisons and square roots in total. The model of computation is exact
real arithmetic and comparisons, with unit-cost square roots of nonnegative
real numbers and complex numbers represented as pairs of real numbers; no
logarithm, floor or bit extraction is used as a primitive operation, and the
integers needed by the algorithm are computed by doubling and comparisons,
at counted cost. Thus the target (3) of the paper,

```math
\lVert D\rVert_2\leq\delta,\qquad
\mathrm{gap}(T+D)\geq c_0(\delta/n)^a,\qquad
\text{at cost } O\bigl(n[1+\log(n/\delta)]^q\bigr)
```

holds with $`c_0=2^{-34}`$, $a=12$ and $q=3$.

The algorithm searches only along the fixed direction $X$. The spectral
function $`F(t)=\sum_{j=1}^n j\lambda_j(T+tX)`$ is convex (Lemma 2.1), and its
centered slope variation

```math
\mathcal S_h(t)=\frac{F(t+h)-F(t)}{h}-\frac{F(t)-F(t-h)}{h}
```

certifies a gap: for $`t\in[0,\delta/n]`$ and $`0<h\leq1`$,
$`\mathcal S_h(t)<1/2`$ implies $`\mathrm{gap}(T+tX)>h^2/(2^{20}n^4)`$
(Proposition 3.1). This uses the tridiagonal structure only once: a
discrete Wronskian identity and a small-leakage cut split a near-degenerate
eigenvalue pair into two approximate eigenvectors on opposite sides of a
coordinate cut (Lemma 3.1), and a nearby auxiliary matrix with a repeated
eigenvalue then forces slope variation at least one (Lemma 3.2).
Algorithm 2 keeps almost half of each window and halves the endpoint slope
variation at each refinement (Lemma 4.2); after at most
$`K=\lceil\log_2(16n^3)\rceil`$ refinements it returns $t,h$ with
$`\mathcal S_h(t)<1/2`$ and $`h>\delta/(128n^4)`$ (Theorem 4.2). Its at most
$3+8K$ evaluations of $F$ are made by the oracle of Lemma 4.3 and
Appendix A, which combines the tridiagonal determinant recurrence, a
balanced product tree and Graeffe root-squaring and costs
$`O(n[1+\log(n/\varepsilon)]^2)`$ operations for accuracy $\varepsilon$.

## Resolution of the catalogue question

The [catalogue statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/3017ea813328900a812c0c105ca16ad6f694857e/eigenvalues-and-inverse-problems/KE-02/README.md)
reads:

> For a Hermitian matrix $H$ with eigenvalues listed with multiplicity,
> define $`\mathrm{gap}(H)=\min_{i\ne j}\lvert\lambda_i(H)-\lambda_j(H)\rvert`$.
> Do universal constants $`a,c_0,C,q>0`$ and a deterministic algorithm exist
> with the following property? For every $n\geq2$, Hermitian tridiagonal
> $`T\in\mathbb C^{n\times n}`$ with $`\lVert T\rVert_2\leq1`$, and
> $`\delta\in(0,1/2)`$, the algorithm receives the three diagonals and
> returns a real diagonal matrix $D$ such that
> $`\lVert D\rVert_2\leq\delta`$ and $`\mathrm{gap}(T+D)\geq c_0(\delta/n)^a`$,
> using at most $`Cn[1+\log(n/\delta)]^q`$ exact arithmetic operations and
> comparisons? Square roots of nonnegative real numbers are allowed at unit
> cost; extracting bits from exact real inputs is not.

Theorem 1.1 meets each requirement.

- **Constants.** $a=12$, $`c_0=2^{-34}`$ and $q=3$; $C$ is the absolute
  constant of the bound $`O(n[1+\log(n/\delta)]^3)`$, which depends on
  neither $n$, $\delta$ nor $T$.
- **Deterministic algorithm.** Algorithm 2 with the oracle of Lemma 4.3:
  every choice is a comparison of computed numbers, and ties go to the left
  window.
- **Inputs.** Every $n\geq2$, every $`\delta\in(0,1/2)`$ and every Hermitian
  tridiagonal $T$ with $`\lVert T\rVert_2\leq1`$, as in Theorem 1.1. The
  algorithm reads the three diagonals: the oracle uses the diagonal entries
  and the squared moduli of the off-diagonal entries, computed from their
  real and imaginary parts (Appendix A).
- **Output.** The real diagonal matrix $D=tX$ with $`t\in[0,\delta/n]`$, so
  $`\lVert D\rVert_2=nt\leq\delta`$.
- **Gap.** The paper's gap is the smallest difference of consecutive
  ordered eigenvalues with multiplicity, which equals the catalogue's
  $`\min_{i\ne j}\lvert\lambda_i-\lambda_j\rvert`$, and
  $`\mathrm{gap}(T+D)>2^{-34}\delta^2n^{-12}\geq2^{-34}(\delta/n)^{12}=c_0(\delta/n)^a`$
  because $`\delta<1`$.
- **Cost and model.** $`O(n[1+\log(n/\delta)]^3)`$ exact arithmetic
  operations, comparisons and unit-cost square roots of nonnegative reals,
  with complex numbers as pairs of reals. No bits are extracted from the
  inputs: no logarithm, floor or bit extraction is used as a primitive
  operation, and the integers $K$ and the number of Graeffe steps are found
  by doubling and comparisons, at counted cost.

The answer to the catalogue question is therefore yes. The bound is in the
exact-arithmetic model of the question; the paper proves no bit-complexity
or finite-precision bound.

## Evidence status

- **Formally proved in Lean 4 with Mathlib:** the finite and scalar core of
  the argument, as one theorem `KE02.coreCertificate : KE02.CoreCertificate`
  in [lean/](lean/README.md), with no hypotheses and exactly the axioms
  `propext`, `Classical.choice` and `Quot.sound`. Its nine components state,
  with all premises explicit: inequality (34) and Lemma 4.2 for every
  $`0<\theta\leq1/4`$; the threshold $K$ found by doubling, $\theta$, the
  constants of Theorem 4.2 and the transcript of Algorithm 2 on every reply
  function whose replies meet the requested accuracies, which terminates
  within $K$ refinements with $`\mathcal S_h(t)<1/2`$, $`h>\delta/(128n^4)`$,
  at most $3+8K$ requests in $`[0,\delta/n]`$, accuracies above
  $`\delta/(2^{16}Kn^4)`$ and $`h^2/(2^{20}n^4)>2^{-34}\delta^2n^{-12}`$;
  Lemma 4.1, one refinement of Algorithm 1 and the constants of Theorem 4.1
  and Remark 4.1; the algebra of Appendix A (the continuant recurrence for
  $`\det(zI+2I+A)`$, the Graeffe transform and its iterates, the coefficient
  and ratio bounds (43), root extraction by square roots, the choice of the
  number of Graeffe steps by doubling, and the index-wise matching with
  weighted error at most $\varepsilon$); and the real inequalities of the
  proofs in Section 3 with the discrete Wronskian identity (22) for the
  coordinate recurrence. The function $F$ is an arbitrary real function;
  where the paper uses Lemma 2.1, its convexity and the secant bounds (9)
  are premises. Lean does not formalize spectral theory, the matrix
  statements of Section 3, the gap conclusions, $`\lVert tX\rVert_2=nt`$, the
  oracle as an algorithm, the model of computation or any operation count;
  [SCOPE.md](lean/SCOPE.md) lists every quantifier and premise.
- **Exact computation:** two standard-library checkers in
  [verification/core/](verification/core/README.md) recompute every constant
  and inequality chain of Sections 2 to 4 and the algebra of Appendix A with
  integer and rational arithmetic and exact Sturm brackets, on finite ranges
  such as $`2\leq n\leq10^4`$ and on fixed instances, and run Algorithms 1
  and 2 as transcripts on exact instances; 18 check families are guarded by
  56 negative controls, and 14 more guard the runner (70 in all). These checks do not establish statements for all
  parameters.
- **Proved in the paper only:** the spectral theory (Lemma 2.1, the
  variational and perturbation formulas of Section 2 and Remark 1.1); the
  localization of Section 3 as matrix statements (Lemmas 3.1 and 3.2 and
  Proposition 3.1); the oracle of Lemma 4.3 and Appendix A as an algorithm;
  the complexity count; and Theorem 1.1 as a whole. The
  [section map](paper-lean-mapping/by-section.md) gives the evidence for
  each numbered result.
- **Numerical illustration:** [verification/numerics/](verification/numerics/README.md)
  contains the code and data of Section 5, which certify the stopping test
  rigorously along a double-precision selection path for six families of
  test matrices up to $n=500$. It is not part of the proof.
- **Review:** the [review record](verification/reviews/README.md) contains
  the independent informal AI-agent audits of an earlier draft, of the
  28-page text before its last editorial corrections, of the Lean statements
  and of the Lean proofs; none requested a mathematical correction.
- **Open:** as the paper states in Sections 5 and 6, whether classical
  localization techniques give a better dimensional dependence than the
  bound $`2^{-34}\delta^2n^{-12}`$, whose worst-case exponent the numerical
  illustrations do not improve; an efficient bit-complexity analysis of the
  certified slope computations, or a numerically better-conditioned
  finite-scale observable; banded and block tridiagonal matrices, possibly
  with several diagonal directions; whether far fewer than $n$ diagonal
  directions suffice for banded matrices, and whether adaptive and
  randomized probes can be turned into an efficient deterministic procedure
  that separates the whole spectrum; larger eigenspace clusters and complex
  Hermitian matrix families; and an end-to-end improvement of a particular
  eigensolver.

## Where to read

Start with the [guide from the question to the checks](paper-lean-mapping/README.md),
then the [paper](paper/main.pdf). The
[section-by-section map](paper-lean-mapping/by-section.md) lists every
numbered result with its Lean fields, exact checks and coverage. The formal
proposition is in [KE02/Statement.lean](lean/KE02/Statement.lean), with its
components in the statement files of [lean/KE02/](lean/KE02/); the
[Lean guide](lean/README.md) and [scope](lean/SCOPE.md) say what they cover.
The [exact-check guide](verification/README.md), the
[exact-check details](verification/core/README.md), the
[numerics guide](verification/numerics/README.md) and the
[verification record](VERIFICATION.md) give reproduction details.

## Reproduce the checks

Use Python 3.11 or later, from the repository root:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
python3 -S -s -B paper-lean-mapping/build_and_check.py
python3 -S -s -B -O paper-lean-mapping/build_and_check.py
python3 -I -B tools/check_markdown_math.py
sha256sum --check SHA256SUMS
```

With the pinned Lean toolchain installed through elan, run from `lean/`:

```sh
export LEAN_NUM_THREADS=4
lake exe cache get
lake build
lake env lean audit/Axioms.lean
python3 -B audit/test_verify.py
python3 -B -O audit/test_verify.py
python3 -B audit/verify.py
python3 -B -O audit/verify.py
```

The numerical illustrations need the packages in
[requirements.txt](verification/numerics/requirements.txt); run from
`verification/numerics/`:

```sh
pip install -r requirements.txt
python3 run_sweep.py
python3 run_arb.py 10 20 50 100
python3 run_direct_s.py A
python3 run_direct_s.py B 100 200 500 1000
python3 run_adaptive.py 50 100 200
python3 run_adaptive.py 500 --families diag_repeated toeplitz
python3 run_fallback.py
python3 make_figures.py
```

The [numerics guide](verification/numerics/README.md) says which files each
command overwrites or appends to. From `paper/`, the paper builds with

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape -outdir=build/ci main.tex
```

as described in the [paper guide](paper/README.md).

## Layout

- `paper/`: manuscript source, two TikZ fragments, figures, bibliography and PDF.
- `lean/`: the pinned Lean project with the statement and proof files in `KE02/`, the aggregate theorem in `KE02.lean`, and the audit scripts and probes in `audit/`.
- `paper-lean-mapping/`: reading guide, result map, machine-readable mapping and its checker.
- `verification/`: one entry point for the exact checks; `core/` holds the exact checkers of the constants and of Appendix A, `numerics/` the code and data of the numerical illustrations, and `reviews/` the review record.
- `tools/`: a static guard for GitHub Markdown math.

## License and citation

Files outside `paper/` are available under the [MIT license](LICENSE).
The files in `paper/`, including the manuscript source and PDF, are licensed
under [CC BY-SA 4.0](paper/LICENSE).
Citation information is in [CITATION.cff](CITATION.cff).

## Acknowledgements

We thank [NetMind.AI](https://www.netmind.ai/) and [AI4ALPHA](https://www.ai4alpha.ca/) for their support of this project. The research of Wenqi Zhu was also supported by the Engineering and Physical Sciences Research Council under grant EP/Y028872/1, *Mathematical Foundations of Intelligence: An "Erlangen Programme" for AI*.
