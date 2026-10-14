# KE-02: deterministic diagonal separation in nearly linear arithmetic time

This document gives the full construction; finite checkers supplement the
written proof and do not replace its all-input arguments.

## Theorem

For every integer n>=2, every Hermitian tridiagonal T of order n with
||T||_2<=1, and every real 0<delta<1/2, a deterministic algorithm returns
a real diagonal D satisfying

    ||D||_2<=delta,
    gap(T+D) > 2^(-88) (delta/n)^42.                         (1)

Its cost is O(n[1+log(n/delta)]^3) exact real arithmetic operations and
comparisons, with square roots of nonnegative reals counted as one
operation. In fact D=t diag(1,...,n) for an adaptively chosen scalar
0<=t<=delta/n. The algorithm extracts no bits of real inputs and returns
only D. All implicit constants are universal.

The polynomial exponent and constant are deliberately conservative.
The construction proves the stronger lower bound

    gap(T+D) > delta^4/(10^12 * 4096^4 * n^42).              (2)

The proof has three ingredients: a small tridiagonal gap produces two
spatially separated approximate eigenvectors; these force a definite
convexity defect under a diagonal tilt; and a scalar interval selection
algorithm finds a small convexity defect with only logarithmically many
function evaluations. Those evaluations have nearly linear arithmetic
cost by an elementary polynomial root-squaring construction.

## 1. Conventions and the weighted spectral function

Eigenvalues of a Hermitian matrix A are listed increasingly, with
multiplicity: lambda_1(A)<=...<=lambda_n(A). Its minimum gap is the
minimum of lambda_(j+1)-lambda_j over 1<=j<n, so a repeated eigenvalue
gives gap zero. Set

    X=diag(1,...,n),
    W=n(n+1)/2,
    f(A)=sum_(j=1)^n j lambda_j(A),
    F(t)=f(T+tX).

The variational formula

    f(A)=max_U tr(U X U* A)                                (3)

holds over unitary U. One elementary proof writes f as the sum, over
k=1,...,n, of the sum of the k largest eigenvalues. For a rank-k
orthogonal projection P, diagonalizing A gives tr(PA)=sum p_i lambda_i,
where 0<=p_i<=1 and sum p_i=k. This is at most the sum of the k largest
eigenvalues, and equality is attained by their spectral projection.
A common increasing eigenbasis attains all k maxima at once, giving (3).

Consequently F is convex. Weyl's eigenvalue inequality also gives

    |f(A)-f(B)|<=W ||A-B||_2<=n^2 ||A-B||_2.                (4)

For s<t, the inequalities (t-s)I<=(t-s)X<=n(t-s)I imply

    W <= (F(t)-F(s))/(t-s) <= nW.                          (5)

These statements allow multiplicities and require no derivatives.

A diagonal unitary gauge changes T to a real symmetric tridiagonal
matrix with nonnegative off-diagonal entries. It commutes with X and
with every real diagonal output D. On each nonzero edge choose its phase
recursively; zero edges cause no difficulty. The proof may therefore
use real eigenvectors. The actual algorithm below need not construct
the gauge: characteristic polynomials use only squared edge magnitudes.

## 2. Two disjoint full-matrix quasimodes from a small gap

Lemma 1. Let H be real symmetric tridiagonal, ||H||_2<=2, with all
off-diagonal magnitudes at most one. Suppose two orthonormal real
eigenvectors u,v have eigenvalues separated by at most h, where

    0<h<=1/(256 n^6).

Let E be their mean and put tau=(16 n^2 h)^(1/4). There are a cut
1<=k<n and real unit vectors a,b supported respectively on {1,...,k}
and {k+1,...,n} such that

    ||(H-EI)a||_2<=2n tau,
    ||(H-EI)b||_2<=2n tau.                                (6)

These are residual bounds in the full matrix H, including leakage
across the cut. Moreover

    <b,Xb>-<a,Xa> >= 1.                                   (7)

Proof. Write the eigenvalues as lambda,mu and put r_i=(u_i,v_i) in R^2,
rho_i=||r_i||_2. Since u,v are orthonormal,

    sum_i r_i^t r_i=I_2,       rho_i<=1.

Cauchy--Binet gives sum_(s<t) det(r_s,r_t)^2=1. In particular some
s<t satisfy |det(r_s,r_t)|>=1/n. Both endpoint row norms are >=1/n.

Write the diagonal entries of H as a_i and its off-diagonal entries as
b_i; their signs will not matter. Telescoping the two eigenvector
recurrences gives the discrete Wronskian identity

    b_i det(r_i,r_(i+1))
        =(mu-lambda) sum_(j<=i) u_j v_j.

Thus |b_i det(r_i,r_(i+1))|<=h. The row recurrence at i is

    b_(i-1) r_(i-1)+(a_i-E)r_i+b_i r_(i+1)=e_i,
    e_i=((lambda-E)u_i,(mu-E)v_i),
    ||e_i||_2<=h rho_i/2.                                 (8)

We claim that between s and t there is either an edge |b_k|<=tau,
or two consecutive rows with rho_k,rho_(k+1)<=tau. Suppose otherwise.
All edges between s and t have magnitude >tau. Since tau<=1/(2n),
both endpoint rows have norm >tau. List all rows in [s,t] whose norms
are >tau. Consecutive indices in this list differ by one or two.

For a nonzero row r define its rank-one direction projection
P_r=r^t r/||r||^2. For two such real rows,

    ||P_r-P_q||_2=|det(r,q)|/(||r|| ||q||).                 (9)

This follows by writing the two unit vectors in an orthonormal basis
of R^2 and computing the two eigenvalues of the projection difference.

For two adjacent large rows, the Wronskian bound and (9) give direction
distance at most h/tau^3<=h/tau^4, since tau<=1.
For large rows at i-1 and i+1 separated by one small row, take the
determinant of (8) with r_(i-1). Because |a_i-E|<=4, every row norm
is <=1, and both neighboring edges have magnitude >tau,

    |det(r_(i-1),r_(i+1))|
      <=4h/tau^2+h/(2tau)
      <=5h/tau^2.

Their direction distance is therefore at most 5h/tau^4. The triangle
inequality along at most n-1 steps in the list gives

    ||P_(r_s)-P_(r_t)||_2
       <=5n h/tau^4=5/(16n)<1/n.

But (9), rho_s,rho_t<=1 and the chosen determinant give a distance
at least 1/n, a contradiction. The claimed cut exists.

Let U be the n by 2 matrix with columns u,v. For the left side, take
the unit coefficient vector c=r_s^t/rho_s. Then w=Uc has norm one,
|(w)_s|=rho_s>=1/n, and ||(H-EI)w||<=h/2. Let Q_L be coordinate
projection onto {1,...,k}. The commutator [H,Q_L]w has just two possibly
nonzero entries, of magnitudes |b_k w_(k+1)| and |b_k w_k|. At a weak
edge its norm is <=tau. At a pair of small rows it is <=sqrt(2)tau,
because |w_i|<=rho_i and |b_k|<=1. Hence

    ||(H-EI)Q_L w||<=h/2+sqrt(2)tau,
    ||Q_Lw||>=1/n.

Normalizing gives the first vector in (6). Use c=r_t^t/rho_t and the
right coordinate projection for the second. Since h<=tau and
1/2+sqrt(2)<2, both residual bounds in (6) follow. The supports are
ordered and disjoint, which gives orthogonality and (7). QED.

## 3. A small gap forces a convexity defect

Lemma 2. Let H satisfy the hypotheses on norm and edges in Lemma 1,
let 0<r<=1, and define f as in Section 1. If

    gap(H)<=h_r := r^4/(10^12 n^14),

then

    f(H+rX)+f(H-rX)-2f(H) >= r/2.                          (10)

Proof. The number h=h_r is positive and satisfies h<=1/(256n^6).
Apply Lemma 1 to a pair attaining the minimum gap. Set zeta=2n tau,
where tau=(16n^2h)^(1/4), and let a,b be its two quasimodes. With
Q=aa^t+bb^t define

    H'=(I-Q)H(I-Q)+EQ.

Both a and b are exact eigenvectors of H' at the common eigenvalue E.
Since ||(H-EI)Q||<=sqrt(2)zeta, expansion gives

    ||H-H'||<=3sqrt(2)zeta<=5zeta.                         (11)

Choose an orthonormal eigenbasis for H' containing a,b. In the block
of equal eigenvalues E, assign two consecutive weights from {1,...,n}
to a,b and fix the assignment to all other eigenvectors. Swapping those
two weights gives two matrices G_+,G_- in the unitary orbit of X, both
maximizing (3) at H'. Choose the orientation so that

    tr((G_+-G_-)X)=<b,Xb>-<a,Xa> >=1.

Using G_+ in (3) at H'+rX and G_- at H'-rX proves

    f(H'+rX)+f(H'-rX)-2f(H') >= r.

Transfer all three terms from H' to H by (4) and (11). The total loss
is at most 4 n^2 * 5zeta=40n^3tau. Now

    (80n^3tau/r)^4=80^4 * 16 /10^12 <1.

Thus 40n^3tau<r/2, proving (10). The argument also covers a repeated
eigenvalue of H: h_r is the positive tolerance supplied to Lemma 1,
so no division by the actual gap occurs. QED.

## 4. Robust scalar interval selection

For a nontrivial interval I=[a,b] of length L, write
S(u,v)=(F(v)-F(u))/(v-u) and define

    P(I)=S(b-L/4,b)-S(a,a+L/4).

Convexity gives P(I)>=0, and (5) gives P(I)<n^3. The two children

    I_left =[a+L/4,a+L/2],
    I_right=[a+L/2,a+3L/4]

have equal length L/4 and satisfy

    P(I_left)+P(I_right)<=P(I).                            (12)

To verify (12), order the four secants defining the two child potentials
by location, with slopes s1<=s2<=s3<=s4. Their sum of differences is
(s2-s1)+(s4-s3)<=s4-s1. The last difference is at most the parent's
outer-quarter secant difference, by monotonicity of convex secants.

If c is the center of I and r=L/4, the same monotonicity gives

    [F(c+r)+F(c-r)-2F(c)]/r <=P(I).                       (13)

Only approximate values of F are needed. For a child length ell,
evaluate each F value with absolute error at most ell/1024. The four
values in its potential, divided by ell/4, give potential error <=1/64.
Choose the child having the smaller computed potential, breaking ties
to the left. Two error allowances and (12) show

    P(I_next)<=P(I)/2+1/32.                              (14)

There are at most eight value queries per round. These bounds allow
arbitrary signs of the individual approximation errors.

Start with I_0=[0,delta/n]. Let K be the least integer with
2^K>=16n^3, found by repeated doubling and comparisons. Iterate the
rule exactly K times and return the midpoint c of I_K. Iterating (14)
gives

    P(I_K)<=2^(-K)P(I_0)+(1/16)(1-2^(-K))<1/8.

Let r be one quarter of the final interval length. Because 2^K<32n^3,

    r=delta/(4n4^K)>delta/(4096n^7).                       (15)

Equations (13)--(15) show

    f(T+(c+r)X)+f(T+(c-r)X)-2f(T+cX)<r/8.                 (16)

All queried parameters, and c-r,c+r, belong to [0,delta/n]. In
particular ||T+cX||<=1+delta<3/2 and its edge magnitudes are <=1.
Also 0<r<1. Applying the contrapositive of Lemma 2 to (16) yields

    gap(T+cX)>r^4/(10^12n^14)
             >delta^4/(10^12*4096^4*n^42).

Since 10^12<2^40, 4096^4=2^48, and delta^4>=delta^42, this proves
(1)--(2). The diagonal D=cX has norm nc<=delta.

## 5. Nearly linear value oracle in the permitted arithmetic model

We give the eigenvalue approximation primitive used for F. It needs no
spectral gap. Intermediate bit lengths are not bounded in this exact
operation model; no bit-complexity claim is being made.

### Polynomial arithmetic

Degree-m polynomials can be multiplied in O((m+1)[1+log(m+1)]) exact
operations using a radix-two Fourier transform. Its power-of-two roots
of unity are permitted constants: starting with i, construct successive
first-quadrant half-angle roots using

    cos(theta/2)=sqrt((1+cos(theta))/2),
    sin(theta/2)=sqrt((1-cos(theta))/2).

Their powers take linear work. All radicands are nonnegative; complex
arithmetic is implemented by pairs of reals with constant overhead.
The usual even/odd transform recursion has logarithmic depth and linear
work per level. Thus this multiplication bound assumes no transcendental
oracle, input bit access, or general algebraic root primitive.

### Characteristic polynomial and Graeffe squaring

Let A be Hermitian tridiagonal, ||A||<=1, and 0<epsilon<1. Write its
diagonal as a_i and squared edge magnitudes as c_i. The polynomial
P(z)=det(zI+2I+A) is computed by the continuant recurrence

    P_(-1)=0, P_0=1,
    P_i(z)=(z+2+a_i)P_(i-1)(z)-c_(i-1)P_(i-2)(z),
    c_0=0.

Encode the recurrence by two-by-two polynomial matrices and multiply
them in a balanced product tree. At each depth the total degrees are
O(n), so the cost is O(n[1+log n]^2).

The roots of P are -r_j, where r_j=2+lambda_j(A) lies in [1,3]. Thus
P(z)=product_j(z+r_j) has strictly positive coefficients. For
P(z)=E(z^2)+zO(z^2), the transformation

    G(P)(z)=E(-z)^2+z O(-z)^2

equals product_j(z+r_j^2): substitute w^2=-z into P(w)P(-w).
After k such steps the roots are -r_j^R, with R=2^k. Each step costs
O(n[1+log n]) operations.

Order the positive r_j decreasingly. Let e_j be the j-th elementary
symmetric function of their R-th powers, with e_0=1. These are the
computed coefficients in descending degree order. Let
p_j=product_(i=1)^j r_i^R. Positivity and the largest-product bound give

    p_j<=e_j<=binom(n,j)p_j<=2^n p_j.

Consequently

    r_j/2^(n/R) <= (e_j/e_(j-1))^(1/R) <= r_j 2^(n/R).     (17)

Choose k by doubling until R>=6n/epsilon. Compute each positive ratio's
R-th root by exactly k successive nonnegative square roots. For
0<=x<=1, convexity gives 2^x<=1+x, and reciprocation gives
2^(-x)>=1-x. Since r_j<=3 and n/R<=epsilon/6<1, (17) proves that
subtracting 2 from these computed roots approximates every eigenvalue
within 3n/R<=epsilon/2 in a matching order. Sorting the approximations
preserves the error against the sorted exact spectrum: the elementary
ordered matching argument bounds each order statistic by the same error.

The total cost, including square roots and sorting, is

    O(n[1+log(n/epsilon)]^2).                              (18)

The recurrence uses squared complex edge magnitudes directly. It
therefore works without computing a phase gauge, including zero edges
and repeated eigenvalues.

### Accuracy and total cost for the selector

At a query t, ||T+tX||<3/2. Apply the preceding routine to
A=(T+tX)/2, then multiply its eigenvalue approximations by two. To
approximate F(t) within E, it suffices to approximate its ordered
eigenvalues within E/W. For a child of length ell, use

    E=ell/1024,       epsilon=ell/(2048 W)

as the accuracy request for the scaled matrix A. The preceding error
bound is at least as strong as required. All requested epsilon are
strictly between zero and one.

The smallest ell is delta/(n4^K)>delta/(1024n^7). Therefore every
oracle call has log(n/epsilon)=O(1+log(n/delta)). There are O(log n)
rounds and at most eight calls per round. Equation (18) gives the total
O(n[1+log(n/delta)]^3) bound, including preparation, comparisons, sorting,
and the n output diagonal entries. Every loop bound is obtained by
integer doubling and comparisons. No logarithm operation is required.

## 6. Explicit algorithm

Input: the three diagonals of T, n>=2, and 0<delta<1/2 under the norm
promise. Set X=diag(1,...,n), W=n(n+1)/2, and I=[0,delta/n].

1. By integer doubling find the least K with 2^K>=16n^3.
2. Repeat K times. Form the two middle-quarter children J of I.
   For each J=[u,v], ell=v-u, query F at u,u+ell/4,v-ell/4,v
   with absolute error ell/1024 using Section 5. Compute
   Phat(J)=4[Fhat(v)-Fhat(v-ell/4)-Fhat(u+ell/4)+Fhat(u)]/ell.
   Retain the child of smaller computed Phat, breaking ties to the left.
3. Let c be the midpoint of the retained interval. Return
   D=diag(c,2c,...,nc).

This is an exact-arithmetic algorithm with approximate spectral value
expressions whose deterministic errors are proved. It is not a random
sampling algorithm, an assumed value oracle, or a quadratic-time
diagonalization. The extreme bit growth possible in the Graeffe routine
is permitted by the stated operation model and is explicitly outside
the scope of this theorem.

Near-linear eigenvalue-only approximation is also given in Aleksandros
Sobczyk, arXiv:2410.21550v2, Appendix C.2, Corollary C.1. The proof here
uses the elementary exact-arithmetic Graeffe construction and does not
depend on importing that paper's FMM assumptions. No novelty claim is
made for root squaring or the polynomial arithmetic primitives.
