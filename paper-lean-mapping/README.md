# A guide from the question to the checks

Given a Hermitian tridiagonal matrix of operator norm at most one, can a
small diagonal perturbation separate every pair of consecutive eigenvalues
efficiently? The [paper](../paper/main.pdf) gives a deterministic construction
for every order n >= 2, including complex edges, zero edges and repeated
eigenvalues. It chooses a single scalar t and returns

```text
D = t diag(1,...,n).
```

The input is supplied through its three diagonals and is promised to
satisfy the structure and norm assumptions. Only D is an output;
eigenvalues and eigenvectors are not required outputs. No rationality,
simple-spectrum or nonzero-edge hypothesis is imposed.

For an arbitrary real budget 0 < delta < 1/2, Theorem 1.1 gives
0 <= t <= delta/n and a minimum eigenvalue gap greater than
2^(-88)(delta/n)^42. The cost is O(n[1+log(n/delta)]^3) exact real
operations and comparisons, with unit-cost nonnegative square roots.
The algorithm extracts no input bits. This is the exact-real theorem;
its cost does not provide a precision or bit-length guarantee.

Theorem 9.1 is a separate finite-bit result. Its inputs are an order,
a dyadic budget delta=2^(-d), and a dyadic componentwise enclosure of the
matrix at the specified precision p=O(log(n/delta)). It returns D=cX with
0 <= nc <= delta/4 and gap greater than 2^(-100) delta^4/n^42, uniformly
for every normalized matrix in that enclosure. The construction uses
O(n^2 p(1+log n)) operations on O(p)-bit integers, or
O(n^2 p^3(1+log n)) schoolbook bit operations. An independent rational
certificate checks the same conditional conclusion for the entire
enclosure; it does not assert that the enclosure contains a normalized
matrix. The verifier may use longer integers.

## Discussion: approximate values, exact arithmetic and finite precision

The exact-real construction requests approximate spectral values. Here
“approximate” describes their proven error relative to the true spectrum;
every arithmetic operation constructing those values is exact in the
stated model. It does not mean that the operations are rounded in a
floating-point format. The interval selector tolerates bounded errors in
its replies, but a floating-point implementation would still need a
separate argument showing that its computed replies meet those bounds.

The Graeffe evaluator needs no pre-existing gap. Its k-th transform has
root parameters r_j^(2^k), where the shifted initial parameters belong to
[1,3]. The paper explicitly allows intermediate quantities with very
large bit lengths; each remains a single value in the exact-real cost
model. The transform E(-z)^2+z O(-z)^2 can involve cancellation.
The accuracy statement for its exact outputs is consequently different
from a theorem about roundoff, conditioning of its intermediate
coefficients, or a fixed working precision. None of those numerical
stability conclusions is asserted here.

The finite-bit construction uses a different value evaluator: integer
inertia counts with signed floor division and a prescribed zero-pivot
replacement. It works with one precision p=O(log(n/delta)) and a supplied
dyadic proxy. Its nearly quadratic bit-operation bound is not obtained
by running the exact Graeffe algorithm at that precision. Reading and
rounding an arbitrary original rational representation carries additional
cost beyond the construction bound, and an arbitrary exact-real input
is not converted to a bit string by this theorem.

For the conditioning of intermediate representations, read the discussion
in [Section 1.2 of the paper](../paper/main.pdf). It distinguishes
conditioning along a reduction chain from the conditioning of its final
root or eigenvalue problem, and matrix backward error from polynomial
backward error. These comparisons do not supply a stability theorem for
the continuant and Graeffe evaluator. Section 1.3 discusses deterministic
tridiagonal eigensolvers with their stated arithmetic and oracle
assumptions. Approximating
the eigenvalues of a prescribed matrix and choosing a perturbation that
separates them are different computational tasks. The paper supplies
both the scalar choice rule and the gap-independent evaluations needed
for that rule; it does not make a floating-point performance comparison.

## Three complementary parts

The written proof connects a convex scalar selection rule to spectral
separation. Set X=diag(1,...,n), and let F(t) be the weighted sum
sum(j lambda_j(T+tX)) of increasingly ordered eigenvalues. A small gap
forces a quantitative centered convexity defect. Approximate values of
F instead select nested intervals with a smaller defect, yielding the
separating tilt. The exact-real evaluator uses continuants and Graeffe
root squaring; the finite-bit evaluator uses safeguarded integer inertia
counts. Their cost arguments use their respective operation models.

The [Lean core](../lean/README.md) proves the scalar selector contract,
universal Graeffe identities, and algebraic coefficient inequalities.
For every convex real function satisfying its initial-potential bound,
and every reply stream satisfying the stated absolute-error contract,
the selector certificate proves the interval, tolerance, radius and defect
bounds, left tie rule, and exactly 8K recorded requests. The polynomial
identities include every finite real root list, with empty lists, zero
roots and repetitions allowed. Positivity and ordering enter only the
coefficient inequalities that require them.

No Lean declaration here proves the complete matrix theorem. In
particular, the Hermitian spectral interpretation, quasimodes,
gap-to-defect implication, analytic ratio-root accuracy and complete
algorithmic cost bounds are paper proofs. There is no formal value-oracle
implementation supplying the selector replies. Counting its recorded
requests does not count the work needed to answer them.

The [exact verification programs](../verification/README.md) use integer
and rational arithmetic for acceptance decisions. They check finite
instances of the identities, selector behavior, constants and input
enclosures, and require corrupted data to fail. The finite-bit constructor
is checked against a separate exact rational inertia verifier. These
checks support the implementations; the all-input quantifiers and
asymptotic bounds come from the written proof. See
[VERIFICATION.md](../VERIFICATION.md) for commands and outputs.

## Follow a result

The [section map](by-section.md) lists all 13 numbered theorems,
propositions, lemmas and remarks in the paper. Every row states the exact
scope of its cited Lean declarations and finite checks. Three additional
rows expose the polynomial ingredients inside Lemma 6.2, using their
equation labels as anchors. Section and equation labels are also recorded
in `other_labels` in [mapping.json](mapping.json).

For the interval argument, start at Lemmas 5.1 and 5.2. The scalar
inequalities have formal counterparts. Proposition 5.3 then combines
the formal scalar outcome with the paper's spectral implications to
produce an actual separating matrix. Its gap conclusion is a paper
proof. Likewise, Lemma 6.2 uses formal polynomial identities, while
its spectral interpretation, approximation guarantee and operation
bound remain in the paper.

For the finite-bit result, follow Theorem 9.1 through the safeguarded
count of Lemma 9.2, fixed-grid brackets and the uniform certificate
bound. Its finite fixtures include orders 2, 3, 4 and 8. Passing those
instances does not prove the general word-size, certificate-size or
runtime theorem. Nearly linear bit complexity and floating-point
stability remain open here.

The rational certificate records ordered spectral brackets at c-r, c
and c+r and an explicit convex-defect upper bound. Its verifier receives
the intended proxy separately, checks agreement with the certificate,
and verifies the brackets by exact rational inertia. Through the paper's
small-gap implication, a valid defect bound gives the stated gap for
every normalized matrix in the componentwise enclosure. It does not
measure the rounding error of an unrelated numerical computation, check
an unavailable exact input against the enclosure, or establish that the
normalized enclosure is nonempty. These distinctions matter when using
the certificate with data from a numerical application.

## Check the map

Run from the repository root with Python 3.11 or later:

```sh
python3 -B paper-lean-mapping/build_and_check.py
python3 -O -B paper-lean-mapping/build_and_check.py
```

Only the Python standard library is required. Both commands leave the
files unchanged and produce the same final line:

```text
PASS: 13 numbered paper results, 3 polynomial ingredients; labels, declarations, exact-check paths and section table; 13 rejection controls
```

The checker follows the paper's explicit input tree, reads its section
and shared theorem counters, and requires an entry for every numbered
result. It verifies labels and numbers, locates cited theorem or lemma
declarations in their stated namespaces, checks the exact-program paths,
and compares the section table byte for byte with its generated text.
Lean comments and strings do not count as declarations. Unsupported
counter changes, missing inputs and malformed map data cause failure.

Thirteen corruption controls exercise missing or duplicate results,
wrong numbers, missing paper labels and inputs, missing or commented-out
Lean declarations, missing exact programs, unknown references and empty
formal evidence. Failure checks remain active under Python `-O`.
This reference check does not compile Lean, execute the mathematical
programs or validate the PDF. Their separate commands are documented in
the [root README](../README.md).

After an intentional change to `mapping.json`, regenerate the section
map explicitly with:

```sh
python3 -B paper-lean-mapping/build_and_check.py --write
```

The command validates the map before writing `by-section.md`.
