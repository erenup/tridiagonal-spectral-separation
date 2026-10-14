# KE-02: deterministic nearly linear diagonal spectral separation

For every n>=2, Hermitian tridiagonal T in C^(n by n) with norm2(T)<=1,
and every real0<delta<1/2, construct a deterministic algorithm returning
real diagonal D with norm2(D)<=delta and

 gap(T+D)>=c0*(delta/n)^a,

using at most C*n*[1+log(n/delta)]^q exact arithmetic operations and
comparisons. Universal a,c0,C,q>0 must be independent of all input.
Square roots of nonnegative reals cost one operation. Extracting bits
from exact real inputs is not allowed. Input is the three diagonals;
only D, not the eigenvalues or eigenvectors, must be output.

Full target quantifies arbitrary normalized Hermitian tridiagonal inputs.
Known weak-coupling, constant-diagonal/equal-coupling, and n=2 cases are
not sufficient. Random perturbation existence alone is not sufficient.
A construction with quadratic or higher cost is not sufficient.
Counterexamples to selected deterministic rules are not a negative answer
to existence of every algorithm. Any full negative answer must respect
that distinction and the exact arithmetic model.
