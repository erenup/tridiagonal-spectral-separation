# Deterministic diagonal spectral separation in nearly linear arithmetic time

The [paper](main.tex) presents the deterministic separation construction,
its proof and the relevant literature. Section 9 adds a separate finite-bit
construction with a uniform input-enclosure certificate. References are in
[refs.bib](refs.bib). Authors: TBD. Acknowledgements: TBD.

Section 1 gives a self-contained overview and a discussion of conditioning
in algebraic rootfinding, intermediate growth in Graeffe iteration, and
the distinct guarantees of exact arithmetic and finite-bit enclosures.
Its open numerical questions do not change the theorem's all-input scope.

## Exact-arithmetic theorem

For every integer $n\geq2$, every Hermitian tridiagonal
$T\in\mathbb C^{n\times n}$ with induced Euclidean norm $\|T\|_2\leq1$,
and every real $0<\delta<1/2$, Theorem 1.1 gives a deterministic
algorithm which, given the three diagonals of $T$, constructs

$$
D=t\operatorname{diag}(1,\ldots,n),\qquad 0\leq t\leq\delta/n,
$$

with $\|D\|_2\leq\delta$ and
$\operatorname{gap}(T+D)>2^{-88}(\delta/n)^{42}$, using
$O(n[1+\log(n/\delta)]^3)$ exact real arithmetic operations and
comparisons. The gap is the minimum consecutive difference of the
increasingly ordered eigenvalues, with multiplicities. Complex edges,
zero edges and repeated eigenvalues of the input are allowed.

Addition, subtraction, multiplication, division by a nonzero real,
comparison, and square roots of nonnegative reals each have unit cost.
The algorithm extracts no input bits. Logarithms occur only in cost
bounds; iteration counts use doubling and comparisons. The structural
and norm hypotheses are promises. Only the diagonal perturbation is
a required output.

This operation bound does not give a bit-complexity or numerical-stability
guarantee: intermediate bit lengths in root squaring can grow very large.
Section 9 uses a different oracle and input model.

## Finite-bit theorem and certificate

For integers $n\geq2$ and $d\geq2$, put $\delta=2^{-d}$ and

$$
a=\min\{k:2^k\geq4n/\delta\},\quad
K=\min\{k:2^k\geq16n^3\},\quad
m=\min\{k:2^k\geq n^2\},\quad p=a+2K+20+m,
$$

where the minima are over nonnegative integers. Set $Q=2^p$,
$\eta=Q^{-1}$, $\beta=2^{-a}$ and $\ell=\beta4^{-K}$.
The finite input consists of $n,d$ and a Hermitian tridiagonal proxy
$T_0$ whose real diagonal and real/imaginary edge components are
multiples of $\eta$ and differ by at most $\eta$ from those of the
promised Hermitian tridiagonal matrix $T$ with $\|T\|_2\leq1$. The entries of $T$ need not be rational
or separately accessible. Reading and rounding an original rational
representation has additional cost.

Theorem 9.1 returns a dyadic $c$ and $D=c\operatorname{diag}(1,\ldots,n)$
with

$$
0\leq nc\leq\delta/4,\qquad
\operatorname{gap}(T+D)>2^{-100}\delta^4/n^{42}.
$$

It uses $O(n^2p(1+\log n))$ integer operations on $O(p)$-bit integers,
or $O(n^2p^3(1+\log n))$ schoolbook bit operations, and $O(np)$ bits
of workspace, with $p=O(\log(n/\delta))$ and universal implicit
constants. There are no square-root, eigenvalue, exact-real-sign or
unbounded-precision-real primitives.

The $O(np)$-bit certificate consists of ordered-eigenvalue enclosures at
$T_0+(c-r)X$, $T_0+cX$, $T_0+(c+r)X$, with
$X=\operatorname{diag}(1,\ldots,n)$ and $r=\ell/4$, and a rational
convexity-defect bound. An independent rational-inertia verifier checks
the intended input, the enclosures and that bound. The same output and
certificate apply to every normalized Hermitian tridiagonal matrix in the
proxy's component enclosure. A passing certificate does not establish
that such a matrix exists. The verifier may use larger intermediate
integers; the bounded-word cost applies to construction.

This is a nearly quadratic finite-bit construction. The nearly linear
finite-precision spectral-value oracle and deterministic regularization
for general nonnormal eigenproblems remain outside the theorem. Neither theorem
asserts floating-point stability or deterministic pseudospectral
shattering for general non-Hermitian matrices.

## Build

Use a TeX installation with `latexmk`, BibTeX and the packages loaded by
`main.tex`. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build main.tex
```

The output is `build/main.pdf`; the included PDF is [main.pdf](main.pdf). The manuscript reads
[sections/finite_bit.tex](sections/finite_bit.tex).

## Proof and supporting checks

In the repository layout, the exact-arithmetic statement and proof are
`../verification/exact-real/proofs/STATEMENT.md` and `../verification/exact-real/proofs/PROOF.md`. The finite-bit statement
and proof are `../verification/finite-precision/proofs/STATEMENT.md` and
`../verification/finite-precision/proofs/PROOF.md`. The paper gives their mathematical
arguments; the finite tests do not prove the all-input claims or costs.

Run both supporting suites from this directory:

```sh
python3 -B ../verification/run.py
```

The first checks finite algebraic identities, residual and spectral-weight
formulas, interval-selection errors and constants. The second checks the
integer constructor and independent rational verifier on exact fixtures
of orders 2, 3, 4 and 8, including complex edges, zero and weak edges,
repeated entries and a rounded nondyadic input. Their registered outputs
and required rejection reasons agree in normal, optimized and alternate
hash-seed modes. Both suites bind their proof and implementation inputs.
The suite guides state the precise control coverage and limitations.

Section 8's integer and rational constant check is included as
[check_constants.py](check_constants.py). Run from this directory:

```sh
python3 -I -B check_constants.py
python3 -I -O -B check_constants.py
```

It checks the original exact-arithmetic curvature constants, child-choice
error allowances, geometric error sum and final exponent comparison.
It does not check Section 9's finite-bit constants. Its three corrupted
constant variants must reject; these checks support the written proof.

## Lean scope

The theorem `KE02.coreCertificate` formalizes the robust scalar
selector with its actual approximate-reply transcript and left-child tie
rule, universal even/odd Graeffe identities, and ordered positive-root
coefficient and ratio bounds. Its component statements specify their
dimension and iteration ranges.

The Hermitian spectral, quasimode and matrix-gap bridges, characteristic
polynomial bridge, spectral value-oracle implementation and accuracy,
analytic root extraction and sorting, and arithmetic or bit complexity
remain outside that Lean theorem. Its query count counts transcript
requests, not the cost of answering them. In particular, it does not
formalize the integer oracle, rational certificate verifier or finite-bit
complexity in Section 9. The repository's `../lean/README.md` and
`../lean/FEASIBILITY_SCOPE.md` give the exact formal scope and audit commands.

## License

The manuscript license is TBD; see [LICENSE](LICENSE).
