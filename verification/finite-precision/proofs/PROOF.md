# A bounded-word oracle and a uniform separation certificate

This proof concerns the fixed finite-information model in STATEMENT.md.
Its sole nonstandard mathematical input is the small-gap
convexity lemma, restated in §1. No bit-complexity claim is imported from a
spectral algorithm in the literature.

## 1. The geometric input and the scalar selector

Let X=diag(1,…,n), W=n(n+1)/2 and
f(H)=Σ_(j=1)^n j λ_j(H), with eigenvalues increasingly ordered. The variational
formula f(H)=max_U tr(UXU*H) makes F(t)=f(T+tX) convex and gives

    |f(A)−f(B)|≤W||A−B||,
    W≤[F(v)−F(u)]/(v−u)≤nW  (u<v).

The [KE-02 proof, §3](../../exact-real/proofs/PROOF.md#3-a-small-gap-forces-a-convexity-defect)
proves the following uniform implication. For a
Hermitian tridiagonal H with ||H||≤2 and edge magnitudes≤1, and 0<r≤1,

    gap(H)≤h(r):=r⁴/(10¹²n¹⁴)
      ⇒ f(H+rX)+f(H−rX)−2f(H)≥r/2.                    (1)

Its proof uses two separated full-matrix quasimodes and a spectral-weight
swap. We use exactly this statement, including its norm and edge hypotheses.

For I=[u,v] of length L define its outer-quarter secant difference

    P(I)=4[F(v)−F(v−L/4)−F(u+L/4)+F(u)]/L.

Convexity gives 0≤P(I)<n³. The two middle-quarter children each have length
L/4 and satisfy P(I_left)+P(I_right)≤P(I). To see this, order the four child
secant slopes s₁≤s₂≤s₃≤s₄; their differences sum to at most s₄−s₁, which
is at most the parent's outer secant difference. Also, at center c and r=L/4,

    [F(c+r)+F(c−r)−2F(c)]/r≤P(I).                     (2)

If each value queried for a child of length ℓ' has error≤ℓ'/1024, its
computed potential has error≤1/64. Choosing the smaller computed child
potential (ties to the left) therefore ensures

    P(I_next)≤P(I)/2+1/32.                              (3)

Starting from [0,β] and iterating K times gives P(I_K)<1/8. In particular
the final center c and r=ℓ/4 satisfy

    Δ_r F(c):=F(c+r)+F(c−r)−2F(c)<r/8.                 (4)

No exact sign of a true spectral expression is needed: the compared values
are the exact dyadic numbers returned by the finite oracle below.

## 2. A safeguarded integer inertia count

Consider any Hermitian tridiagonal A whose diagonal and real/imaginary edge
components are multiples of η=1/Q. Write its diagonal as A_i/Q and its
squared edge magnitudes as C_i/Q², where C_i=B_i²+Z_i²≥0 is an integer.
At the grid shift x=M/Q, form integer pivots

    D₁=A₁−M; replace D₁=0 by −1;
    D_i=A_i−M−floor(C_(i−1)/D_(i−1)); replace D_i=0 by −1.

Every denominator is nonzero. Let ν be the number of negative D_i. Then
there exists a real diagonal E with ||E||≤η such that

    ν = number of eigenvalues of A+E strictly below x,
    x is not an eigenvalue of A+E.                      (5)

Proof. Put d_i=D_i/Q. Without the zero replacement, the error relative to
the exact scalar LDL recurrence is

    e_i = η[C_(i−1)/D_(i−1)−floor(C_(i−1)/D_(i−1))]∈[0,η).

Replacing a zero integer pivot by −1 subtracts η from this error, leaving
e_i∈[−η,0). At i=1 the error is either 0 or −η. Thus the computed pivots
are EXACT LDL pivots of A+diag(e_i)−xI. The off-diagonal entries are unchanged;
complex entries cause no problem because only their squared magnitudes enter.
The unit lower bidiagonal factor is nonsingular. Sylvester's inertia law
therefore proves (5), and the product of the nonzero pivots proves
nonsingularity. This proof allows zero edges and repeated eigenvalues of A.

For every j, Weyl's inequality and (5) give the safe decisions

    ν≥j ⇒ λ_j(A)<x+η,
    ν<j ⇒ λ_j(A)>x−η.                                  (6)

The auxiliary E may depend on x; the implications refer to the same original
A, so no consistency of these auxiliary matrices across queries is required.

## 3. Fixed-grid bisection of all ordered eigenvalues

Assume ||A||<2. For each j=1,…,n initialize integer endpoints L=−2Q,U=2Q.
Repeat exactly p times:

    M=floor((L+U)/2);
    compute ν by §2;
    if ν≥j: U=min(U,M+1);
    otherwise: L=max(L,M−1).

Equations (6) preserve L/Q<λ_j(A)<U/Q. If w=U−L, the next integer width
is at most ceil(w/2)+1≤w/2+3/2. Since w₀=4Q, after p steps

    w_p≤4+3(1−2^(−p))<7.                               (7)

In particular the returned interval has width≤7η, and its midpoint
approximates λ_j(A) within (7/2)η. Intervals are indexed by j; sorting
midpoints is unnecessary, including when A has repeated eigenvalues.

This algorithm performs O(n²p) integer operations. Suppose |A_i|≤2Q,
|B_i|,|Z_i|≤Q+1 and |M|≤2Q, as will hold for every application below.
Then C_i≤8Q², and induction using |D_(i−1)|≥1 gives

    |floor(C_i/D_(i−1))|≤8Q²+1,
    |D_i|≤13Q².

Every recurrence integer therefore has at most 2p+O(1) bits; no rational
numerator or denominator is propagated. Addition, multiplication and signed
floor division of these integers cost O(p²) bit operations by elementary
algorithms. The oracle cost is O(n²p³) bit operations, with O(np) storage.
This is an explicit word-size bound, not an exact-real operation count.

## 4. Value queries from a single input enclosure

Let T₀ be the supplied proxy. If each diagonal component error is at most η
and each real/imaginary edge error at most η, the absolute error in one
complex edge is at most 2η. The Hermitian error matrix has row sums at most
5η. Therefore, for EVERY admissible T in that enclosure,

    ||T−T₀||≤5η.                                       (8)

All query parameters t belong to [0,β]. Their dyadic denominators divide
2^(a+2K+2), which divides Q. Hence T₀+tX is represented exactly on the fixed
grid. Its norm is at most 1+5η+nβ<2, because nβ≤δ/4≤1/16 and p≥20.
Its grid entries satisfy the size bounds used in §3.

At t compute the n intervals of §3 and let F̂(t) be the sum of their
midpoints weighted by j. The error against f(T₀+tX) is at most (7/2)Wη.
By (8), its error against F(t)=f(T+tX) is at most

    (17/2)Wη≤9n²η≤9ℓ/2²⁰<ℓ'/1024                    (9)

for every child length ℓ'≥ℓ. Thus one fixed precision p suffices for all
adaptive queries and all matrices represented by the enclosure. The
comparison in §1 may be implemented without division: both children have
the same length, so compare just the integer numerators of their four-value
differences. Ties are decided deterministically. All these numerators have
O(p+log n)=O(p) bits.

Applying §1 now proves (4) for every admissible T, with the SAME chosen c.
The actual matrix H=T+cX has norm≤1+δ/4<2 and unchanged edges of magnitude
≤1; also 0<r<1. The contrapositive of (1) gives gap(T+cX)>h(r).

Finally, 2^K<32n³ and β>δ/(8n), so

    r=β/(4·4^K)>δ/(2¹⁵n⁷),
    h(r)>δ⁴/(10¹²·2⁶⁰n⁴²)>2^(−100)δ⁴/n⁴².           (10)

The output budget follows from 0≤c≤β and nβ≤δ/4.

## 5. A certificate for an entire input enclosure

Run §3 at t_−=c−r,t₀=c,t_+=c+r. For each such t retain all n intervals
[l_j(t),u_j(t)] of width≤7η. These enclose the increasingly ordered
spectrum of T₀+tX. Define

    L(t)=Σj·l_j(t),       U(t)=Σj·u_j(t),
    B=U(t_+)+U(t_−)−2L(t₀)+20Wη.                       (11)

For every admissible T, (8) implies Δ_r F(c)≤B. Moreover each true value
F(t) lies between L(t)−5Wη and U(t)+5Wη, an interval of length≤17Wη.
Consequently B−Δ_r F(c)≤68Wη. Since n²η≤ℓ/2²⁰=4r/2²⁰,

    B<r/8+68r/2¹⁸<r/4<r/2.                            (12)

Thus the certificate passes with strict slack. To verify it, check the
parameter and budget bounds, the three sets of ordered spectral enclosures,
and the exact rational inequality B<r/2. Equations (1), (8) and (11) then
prove gap(T+cX)>h(r) simultaneously for all normalized T in the enclosure.
This is a deterministic mathematical certificate, not a floating-point test
of a selected sample matrix.

The spectral intervals can be checked independently by exact rational
inertia. For a Hermitian tridiagonal A−xI, a nonzero first pivot is eliminated
by a 1×1 Schur complement and contributes its sign. A zero first pivot with
zero next edge contributes one zero and is removed. A zero first pivot with
nonzero next edge forms a 2×2 block of determinant −|b|²<0, contributing one
positive and one negative eigenvalue. The (2,2) entry of that block's inverse
is zero, so eliminating it leaves the next diagonal unchanged. Repeat these
rules. They give the exact number N_<(x) of eigenvalues strictly below x,
including at eigenvalue endpoints and with zero edges. For each claimed
j-th bracket, require N_<(l_j)<j and N_<(u_j)≥j. These imply
l_j≤λ_j<u_j. This exact rational checker is different from the safeguarded
fixed-grid construction and uses no numerical eigenvalue routine.

The certificate has three pairs of n grid endpoints, plus O(1) parameters
and the n-entry input proxy, hence O(np) bits. The verifier may have larger
intermediate exact integers; no bounded-word verification cost is claimed.

## 6. Total complexity and what remains open

There are at most 8K value calls for selection and three for certification.
Each uses O(n²p) integer operations on O(p)-bit words. Parameter construction,
entry squaring, weighted summation and the n diagonal output entries fit
within the same bound. Therefore total cost is

    O(n²p(1+log n)) bounded-word integer operations,
    O(n²p³(1+log n)) schoolbook bit operations,
    O(np) workspace.

All exponents and constants are uniform in n,d and the input entries.
Since a=O(d+log n), K,m=O(log n), the precision p=O(log(n/δ)). The input
representation and rounding cost are stated separately in STATEMENT.md.

The open near-linear finite-bit target is unchanged: obtain certified
weighted spectral values to the needed inverse-polynomial absolute accuracy
in O(n·polylog(n/δ)) bit operations or comparable bounded-word work. The
present n independent bisections do not achieve this. A nearly linear exact
arithmetic Graeffe oracle cannot simply be assigned the fixed precision above:
its coefficient transformations have large cancellation, unlike §2.
