# Finite-bit certified diagonal regularization

For every integer n≥2 and integer d≥2 put δ=2^(−d). Let T be an arbitrary
complex Hermitian tridiagonal matrix with ||T||₂≤1. Set

- a=min{k:2^k≥4n/δ}, β=2^(−a);
- K=min{k:2^k≥16n³}, ℓ=β4^(−K);
- m=min{k:2^k≥n²}, p=a+2K+20+m, Q=2^p, η=Q^(−1).

The finite input is n,d and a Hermitian tridiagonal dyadic proxy T₀ whose
real diagonal entries and real/imaginary off-diagonal components are integer
multiples of η, each differing from the corresponding component of T by at
most η. This is an enclosure/finite-information model; arbitrary exact real
inputs are not silently treated as finite strings. The input comprises O(np)
bits under the norm promise. For rational data, the cost of reading and
rounding the original representation is additional to the construction cost.

There is a deterministic integer algorithm returning a dyadic c and the real
diagonal D=c diag(1,…,n), with

    0≤nc≤δ/4,
    gap(T+D)>2^(−100) δ⁴/n⁴²,

using O(n² p(1+log n)) integer operations on O(p)-bit integers, hence
O(n² p³(1+log n)) elementary bit operations by schoolbook arithmetic, and
O(np) bits of workspace. Here p=O(log(n/δ)). There are no square-root,
eigenvalue, unbounded-precision-real, or exact-real-sign primitives.

The algorithm also outputs O(np) bits of certificate data: three sets of
rational ordered-eigenvalue enclosures for T₀+(c−r)X, T₀+cX and T₀+(c+r)X,
where X=diag(1,…,n), r=ℓ/4, and an explicit rational convex-defect bound.
An independent exact rational verifier checks these enclosures and the defect
inequality. The same certificate proves the gap bound uniformly for every
normalized Hermitian tridiagonal matrix in the componentwise η-enclosure
centered at T₀. The verifier may use longer exact integers; the bounded-word
claim concerns the construction.

This is a finite-bit baseline at nearly quadratic, not nearly linear, cost.
No novelty is claimed for safeguarded Sturm counting or bisection. The result
is their explicit integration with the convex-defect regularization mechanism
and a uniform input-enclosure certificate. It does not solve IE-07 or establish
the missing nearly linear finite-precision spectral-value oracle. Dyadic
budgets lose no qualitative generality: for an arbitrary requested real budget
0<ε<1/2, a supplied dyadic δ with ε/2≤δ≤ε (and δ≤1/4) yields the same bounds
with only an absolute-factor change in the gap constant.
