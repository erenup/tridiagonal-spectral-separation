# Scalar-selector and polynomial core

Pinned environment: Lean v4.34.0-rc2; Mathlib
85e3a25e006c35636f0e53b0e9296caca2685bc0.

The target is `KE02.coreCertificate : KE02.CoreCertificate`, with no
hypotheses at the aggregate level. Component structures state every
mathematical hypothesis explicitly. The mathematical reference is the [paper](../paper/main.pdf),
Sections 5–6.

## What the target certifies

For every integer n>=2 and real 0<delta<1/2, every real function convex
on [0,delta/n] with initial quarter-secant potential <n^3, and every
reply stream obeying the per-request absolute-error bound, the actual
recursive selector has the complete outcome in SelectorStatement.lean.
Each round obtains four separate replies for each middle-quarter child,
chooses the smaller estimated potential, and breaks ties to the left.
The replies may have arbitrary signs of error and may disagree at repeated
query points. A recorded transcript ties the replies to the same recursion.
No convergence or continuity premise is imposed on the reply stream.

The outcome includes least-threshold properties for K=min{k:2^k>=16n^3},
positive nested intervals, all queries within [0,delta/n], positive
child-length/1024 tolerances, estimate error <=1/64, the child-potential
sum bound, one-step and all-prefix potential bounds, exactly 8K recorded
calls, and final radius delta/(4n4^K)>delta/(4096n^7), potential <1/8,
and symmetric convexity defect <radius/8.

For every finite n (including zero) and arbitrary real roots r_i
(including zero and repetitions), the actual even/odd coefficient split
reconstructs the polynomial, and the coefficient-defined Graeffe map sends
product(X+r_i) to product(X+r_i^2). Its k-th iterate, for every natural k,
produces product(X+r_i^(2^k)). The transform is not defined using the desired
root identity.

The coefficients are defined from that actual polynomial product. Their
finite subset expansion and leading coefficient are universal. For positive
roots, every coefficient in descending degree order is positive. For
positive roots in decreasing order and every j<=n, the first-j product p_j
and actual coefficient e_j satisfy
p_j<=e_j<=choose(n,j)p_j<=2^n p_j. For every i<n, the adjacent ratio lies
between r_i^(2^k)/2^n and 2^n*r_i^(2^k).

## What is outside this target

The target does not formalize Hermitian spectral convexity, discrete
Wronskian/quasimode arguments, the small-gap-to-convexity bridge, the matrix
eigenvalue gap or diagonal perturbation conclusion, the connection between
tridiagonal characteristic polynomials and the roots, a spectral value oracle implementation, or a proof that such an oracle
supplies replies satisfying the selector's error premise.

The scalar ratio-root accuracy extension (successive square roots,
2^(n/R) bounds, eigenvalue approximation and sorting) is not included in
the Lean core. The algebraic ratio bounds above are included.
FFT/product-tree implementations, arithmetic cost bounds, bit-access
restrictions as operational semantics, bit complexity and the full
nearly-linear matrix algorithm remain outside Lean. The 8K conclusion counts
requests in the defined transcript, not the cost of answering them.

The core is uniform in all its displayed dimensions and iteration counts.
No numerical sample, finite test family or extra target-shaped assumption
stands in for one of those quantifiers. Standard proof terms must establish
the fixed statements without sorry, admit, additional axioms or native
checking. Separate exact tests and source/configuration controls supplement
the clean kernel build; they do not act as theorem premises.
