# From the catalogue question to the checks

The catalogue question KE-02 asks for universal constants $`a,c_0,C,q>0`$ and
a deterministic algorithm that, for every $n\geq2$, every Hermitian
tridiagonal $`T\in\mathbb C^{n\times n}`$ with $`\lVert T\rVert_2\leq1`$ and
every $`\delta\in(0,1/2)`$, returns a real diagonal $D$ with
$`\lVert D\rVert_2\leq\delta`$ and $`\mathrm{gap}(T+D)\geq c_0(\delta/n)^a`$,
using at most $`Cn[1+\log(n/\delta)]^q`$ exact arithmetic operations and
comparisons, with unit-cost square roots of nonnegative reals and no bit
extraction from the inputs.

Theorem 1.1 of the paper answers it with $a=12$, $`c_0=2^{-34}`$ and $q=3$:
Algorithm 2 with the oracle of Lemma 4.3 returns $D=tX$ with
$`t\in[0,\delta/n]`$ and

```math
\lVert D\rVert_2\leq\delta,\qquad
\mathrm{gap}(T+D)>2^{-34}\frac{\delta^2}{n^{12}}\geq2^{-34}\Bigl(\frac{\delta}{n}\Bigr)^{12}.
```

| Symbol | Meaning |
| --- | --- |
| $X$ | The fixed diagonal direction $`\mathrm{diag}(1,\ldots,n)`$ |
| $`H(t)`$ | $T+tX$ for $`0\leq t\leq\delta/n`$ |
| $`F(t)`$ | The spectral function $`\sum_{j=1}^n j\lambda_j(H(t))`$, convex by Lemma 2.1 |
| $`\mathcal S_h(t)`$ | The centered slope variation (13) over the window $`[t-h,t+h]`$ |
| $`\mathcal S_h^{(\theta)}(t)`$ | The endpoint slope variation (33) |
| $K$, $\theta$ | $`K=\lceil\log_2(16n^3)\rceil`$ refinements and $`\theta=1/(4K)`$ in Algorithm 2 |
| $`e_j`$, $`p_j`$ | The coefficients of the Graeffe iterate and the leading root products of Appendix A |

## The argument in four steps

1. **A convex spectral function (Section 2).** $F$ is convex and
   increasing, with secant slopes between $`n(n+1)/2`$ and $`n^2(n+1)/2`$;
   its slope variation measures how fast the eigenvalues change their
   relative motion.
2. **The local gap certificate (Section 3).** For $`0<h\leq1`$,
   $`\mathcal S_h(t)<1/2`$ implies $`\mathrm{gap}(H(t))>h^2/(2^{20}n^4)`$.
   A discrete Wronskian identity and a small-leakage cut split a
   near-degenerate pair across a coordinate cut (Lemma 3.1), and a nearby
   auxiliary matrix with a repeated eigenvalue forces slope variation at
   least one (Lemma 3.2, Proposition 3.1).
3. **The selector (Section 4).** Algorithm 2 keeps almost half of each
   window and halves the endpoint slope variation (Lemma 4.2), so after at
   most $K$ refinements it returns a window with $`\mathcal S_h(t)<1/2`$ and
   $`h>\delta/(128n^4)`$ (Theorem 4.2), hence the gap bound $`2^{-34}\delta^2n^{-12}`$.
4. **The oracle (Lemma 4.3 and Appendix A).** The determinant recurrence,
   a balanced product tree and Graeffe root-squaring give $F(t)$ to
   accuracy $\varepsilon$ in $`O(n[1+\log(n/\varepsilon)]^2)`$ exact
   operations, comparisons and square roots, which with the smallest
   requested accuracy (40) gives the total $`O(n[1+\log(n/\delta)]^3)`$.

Read [by-section.md](by-section.md) alongside the [paper](../paper/main.pdf).
It lists every numbered result, with its label and page, and eight
supporting anchors, each with its Lean fields, exact checks, numerical
illustrations and an explicit statement of what is and is not covered.
[mapping.json](mapping.json) records the same data in machine-readable form.

## What each kind of evidence establishes

**Lean 4 with Mathlib.** The theorem
`KE02.coreCertificate : KE02.CoreCertificate` in [lean/](../lean/README.md) has
no hypotheses. Its nine components state, with all premises explicit:
inequality (34) and Lemma 4.2; $K$, $\theta$, the constants of Theorem 4.2
and the run of Algorithm 2 on every reply function whose replies meet the
requested accuracies (Theorem 4.2 without Proposition 3.1); Lemma 4.1, one
refinement of Algorithm 1 and the constants of Theorem 4.1 and Remark 4.1;
the algebra of Appendix A (the continuant recurrence, the Graeffe transform,
the coefficient bounds, root extraction and the index-wise matching); and
the real inequalities of Section 3 with the discrete Wronskian identity
(22). Where the paper uses Lemma 2.1, the Lean statements take an arbitrary
real function $F$ and assume its convexity and the secant bounds (9). The
kernel dependencies are exactly `propext`, `Classical.choice` and
`Quot.sound`.

Lean does not formalize spectral theory, Lemma 2.1, the matrix statements
of Section 3 including Proposition 3.1, the gap conclusions (38) and of
Theorem 4.1, $`\lVert tX\rVert_2=nt`$, the oracle of Lemma 4.3 as an algorithm,
the model of computation, or any operation count. Theorem 1.1 is therefore
not a Lean theorem; its scalar part is. The [scope](../lean/SCOPE.md) lists
every quantifier and premise.

**Exact computation.** The checkers in
[verification/core/](../verification/core/README.md) recompute the constants
and inequality chains of Sections 2 to 4 and the algebra of Appendix A with
integer and rational arithmetic, on finite ranges such as
$`2\leq n\leq10^4`$ and on fixed instances, and run both algorithms as
transcripts on exact instances. Each family has negative controls that must
be rejected. These checks can detect a wrong constant, sign or index; they
do not prove statements for all parameters.

**Written proofs.** Everything else, including Theorem 1.1 as a whole, is
proved in the paper.

**Numerical illustration.** The code and data in
[verification/numerics/](../verification/numerics/README.md) produce Section 5.
They are not part of any proof and are not run by the exact checks.

## Check the correspondence

From the repository root, run:

```sh
python3 -S -s -B paper-lean-mapping/build_and_check.py
python3 -S -s -B -O paper-lean-mapping/build_and_check.py
```

The standard-library script indexes the TeX sources in order, following the
two included fragments: the section counter (with the appendix lettered),
the separate counter of each theorem-like environment, the global counters
of algorithms, equations, figures and tables, every label with the number it
receives, and the title of every numbered result. It indexes the Lean
library after masking comments and strings: top-level declarations, the
fields of every structure, the field assignments of the component proofs and
the anonymous constructor of `KE02.coreCertificate`. It requires that the
nine components appear in the order of the fields of `KE02.CoreCertificate`,
that each component proof assigns exactly the fields of its structure, that
every field of every component and of `KE02.Algorithm2Outcome` is mapped once
to exactly the declarations its proof cites, that every mapped exact-check
function exists and its family is listed in `CHECKERS.txt`, that every
numerics file exists, and that the two tables in [by-section.md](by-section.md)
equal the tables generated from the mapping and name every mapped field,
check and numerics file. Coverage classes are tied to the references: a
formalized entry must cite Lean fields, an exact-only entry must cite checks
and no Lean field, and a written-only entry cites neither.

A missing or renamed label, numbered result, title, paper input, Lean file,
declaration, structure field, exact-check function or family, or numerics
file makes the script fail, with a message naming the failed requirement, as
does a source line that the indexer cannot parse. Forty-five in-memory
negative controls exercise these rejections without changing any file. Both
commands print the same output. The script does not compile Lean, build the PDF, run the exact checks
or run the numerical illustrations, and page numbers are data checked only
for range and order; the build and run commands are in the
[Lean guide](../lean/README.md), the
[exact-check guide](../verification/README.md) and the
[verification record](../VERIFICATION.md).
