# Deterministic diagonal spectral separation in nearly linear arithmetic time

Authors: TBD

Repository: [erenup/tridiagonal-spectral-separation](https://github.com/erenup/tridiagonal-spectral-separation).

Read the [paper](paper/main.pdf) and its [LaTeX source](paper/main.tex).
The construction answers the [catalogue question](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/eb7c9d64f91757a82fbe9167e80ab9c1b7f36c22/eigenvalues-and-inverse-problems/KE-02/README.md)
in its specified exact-real arithmetic model, with universal exponents
$a=42$, $q=3$ and gap constant $c_0=2^{-88}$.
The separate finite-bit theorem has a different input and cost model.

The result supplies deterministic spectral separation for the full
promised tridiagonal input class, including repeated eigenvalues, by
choosing a single diagonal tilt in $O(\log n)$ rounds. For readers
interested in conditioning and algebraic rootfinding, the paper begins
with the construction and a discussion of its intermediate polynomial
representations. It distinguishes the resolved exact-operation question
from open questions about roundoff and nearly linear bit complexity.

## Exact-arithmetic theorem

For every integer $n\geq2$, every Hermitian tridiagonal
$T\in\mathbb C^{n\times n}$ with induced Euclidean norm $\lVert T\rVert_2\leq1$,
and every real $0\lt\delta\lt1/2$, Theorem 1.1 gives a deterministic
algorithm which, given the three diagonals of $T$, constructs

$$
D=t\mathrm{diag}(1,\ldots,n),\qquad 0\leq t\leq\delta/n,
$$

with $\lVert D\rVert_2\leq\delta$ and
$\mathrm{gap}(T+D)\gt2^{-88}(\delta/n)^{42}$, using
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
promised Hermitian tridiagonal matrix $T$ with $\lVert T\rVert_2\leq1$. The entries of $T$ need not be rational
or separately accessible. Reading and rounding an original rational
representation has additional cost.

Theorem 9.1 returns a dyadic $c$ and $D=c\mathrm{diag}(1,\ldots,n)$
with

$$
0\leq nc\leq\delta/4,\qquad
\mathrm{gap}(T+D)\gt2^{-100}\delta^4/n^{42}.
$$

It uses $O(n^2p(1+\log n))$ integer operations on $O(p)$-bit integers,
or $O(n^2p^3(1+\log n))$ schoolbook bit operations, and $O(np)$ bits
of workspace, with $p=O(\log(n/\delta))$ and universal implicit
constants. There are no square-root, eigenvalue, exact-real-sign or
unbounded-precision-real primitives.

The $O(np)$-bit certificate consists of ordered-eigenvalue enclosures at
$T_0+(c-r)X$, $T_0+cX$, $T_0+(c+r)X$, with
$X=\mathrm{diag}(1,\ldots,n)$ and $r=\ell/4$, and a rational
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

## Evidence status

- **Formally proved in Lean 4 with Mathlib:** `KE02.coreCertificate`
  proves the robust scalar interval selector using its actual approximate
  replies and left-child tie rule, universal even/odd Graeffe identities,
  and ordered positive-root coefficient and ratio bounds. The selector's
  query count counts transcript requests. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur in the theorem's axiom closure.
- **Exact computation:** Python standard-library integer and rational
  checks verify finite continuant and Graeffe identities, coefficient
  ratios, interval-selection error bounds, residual and spectral-weight
  identities, and numerical constants. The finite-bit suite constructs
  and verifies enclosure certificates on exact fixtures of orders 2, 3,
  4 and 8, including complex, zero and weak edges and repeated entries.
  Corrupted inputs and incomplete inventories must be rejected, with
  identical results under normal and optimized Python execution.
- **Proved in the paper only:** the all-input spectral-separation
  theorems and their arithmetic and bit-complexity bounds; the Hermitian
  spectral, quasimode and matrix-gap arguments; the characteristic-polynomial
  bridge, value-oracle implementation and accuracy, root extraction and
  sorting; and the integer oracle and rational certificate-verifier
  guarantees. The scalar and polynomial Lean core proves only the
  components identified in the [result map](paper-lean-mapping/by-section.md).
  Finite examples do not prove the quantified theorems or complexity bounds.
- **Open:** a nearly linear bit-complexity construction for this full input
  class, a nearly linear finite-precision spectral-value oracle, and
  deterministic regularization for general nonnormal eigenproblems.
  Neither theorem establishes floating-point stability or deterministic
  pseudospectral shattering for general non-Hermitian matrices.

## Where to read

Start with the [guide from the question to the checks](paper-lean-mapping/README.md),
then the [paper](paper/main.pdf). Section 1 states the exact-real theorem,
Sections 2–7 prove it, Section 8 describes finite supporting checks, and
Section 9 states and proves the separate finite-bit theorem.

The [section-by-section map](paper-lean-mapping/by-section.md) records each
numbered result and its precise evidence. The
[Lean guide](lean/README.md), [exact-check guide](verification/README.md)
and [verification record](VERIFICATION.md) describe reproduction and scope.

## Reproduce the checks

Use Python 3.11 or later for the standard-library checks:

```sh
python3 -B verification/run.py
python3 -O -B verification/run.py
python3 -B paper-lean-mapping/build_and_check.py
python3 -O -B paper-lean-mapping/build_and_check.py
```

For the formal core, install Lean through elan, fetch the pinned Mathlib
cache, and run the verifier:

```sh
cd lean
lake exe cache get
python3 -B verify.py
```

The Lean guide states the pinned versions, memory requirements and output
options. Do not update dependencies when reproducing the recorded check.
The [paper guide](paper/README.md) gives the LaTeX build command.

## Layout

- `paper/`: manuscript source, bibliography, built PDF and exact constant check.
- `lean/`: pinned Lean project and formal-core verifier.
- `paper-lean-mapping/`: reading guide, result map and reference checker.
- `verification/`: exact-real and finite-bit checks with one entry point.

## License

Files outside `paper/` are available under the [MIT license](LICENSE).
The [paper license](paper/LICENSE) is TBD.

## Citation

Author information is TBD in [CITATION.cff](CITATION.cff).

## Acknowledgements

TBD.
