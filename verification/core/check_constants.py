#!/usr/bin/env python3
"""Exact finite cross-checks of the constants and inequality chains in
"A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices".

Python standard library only. Every decision is taken with exact integer or
rational arithmetic (fractions.Fraction); square roots enter only through
rational brackets lo <= sqrt(x) < hi that are verified by exact squaring.
Statements that are universal in n or K are checked on the finite ranges
printed in the output; such checks are finite cross-checks, not proofs.
Every check family runs negative controls (deliberately wrong constants or
inputs); the run fails if a control is accepted.

Locators (Lemma 3.1, (37), ...) refer to the numbering printed in the final
version of the paper.

Usage:  python3 -S -s -B check_constants.py [--inject-fault]
Exit status 0 and final line "RESULT: PASS check_constants.py: ..." on success.
"""

import sys
import hashlib
from fractions import Fraction as Q
from math import isqrt

NAME = "check_constants.py"
N_MAX = 10000          # finite range n = 2..N_MAX for statements universal in n
K_MAX = 1024           # finite range K = 1..K_MAX for statements universal in K
BITS = 192             # precision of the rational square-root brackets
HALF = Q(1, 2)
FAULT = [False]        # set by --inject-fault (end-to-end control of the fail-closed path)


# ---------------------------------------------------------------- exactness guards

def _x(v):
    if type(v) is bool or not isinstance(v, (int, Q)):
        raise TypeError("non-exact operand in a decision: " + type(v).__name__)
    return v


def LT(a, b):
    return _x(a) < _x(b)


def LE(a, b):
    return _x(a) <= _x(b)


def EQ(a, b):
    return _x(a) == _x(b)


def GT(a, b):
    return _x(a) > _x(b)


def GE(a, b):
    return _x(a) >= _x(b)


def ALL(items):
    for v in items:
        if v is not True:
            return False
    return True


# ---------------------------------------------------------------- deterministic data

class Rng:
    """SHA-256 in counter mode: integer data independent of the random module and of the Python version."""

    def __init__(self, label):
        self.key = hashlib.sha256(b"KE-02 exact checks/" + label.encode("ascii")).digest()
        self.ctr = 0
        self.buf = b""

    def _take(self, k):
        while len(self.buf) < k:
            self.buf += hashlib.sha256(self.key + self.ctr.to_bytes(8, "big")).digest()
            self.ctr += 1
        out, self.buf = self.buf[:k], self.buf[k:]
        return out

    def below(self, m):
        if m <= 0:
            raise ValueError("empty range")
        nbits = m.bit_length()
        nbytes = (nbits + 7) // 8 + 1
        while True:
            v = int.from_bytes(self._take(nbytes), "big") >> (8 * nbytes - nbits)
            if v < m:
                return v

    def integer(self, lo, hi):
        return lo + self.below(hi - lo + 1)

    def rational(self, lo, hi, den):
        lo, hi = Q(lo), Q(hi)
        a = -((-lo.numerator * den) // lo.denominator)
        b = (hi.numerator * den) // hi.denominator
        return Q(self.integer(a, b), den)

    def nonzero(self, lo, hi, den):
        while True:
            v = self.rational(lo, hi, den)
            if v != 0:
                return v


# ---------------------------------------------------------------- exact helpers

def sqrt_bracket(x, bits=BITS):
    """Rationals lo, hi with lo >= 0, lo^2 <= x < hi^2 and hi - lo = 2^-bits (verified exactly)."""
    x = Q(x)
    if x < 0:
        raise ValueError("negative radicand")
    a = isqrt((x.numerator << (2 * bits)) // x.denominator)
    lo, hi = Q(a, 1 << bits), Q(a + 1, 1 << bits)
    if not (lo * lo <= x and x < hi * hi):
        raise ArithmeticError("square-root bracket failed")
    return lo, hi


def fdiv(a, b):
    return Q(a) / Q(b)


def identity(n):
    return [[Q(1) if i == j else Q(0) for j in range(n)] for i in range(n)]


def mat_mul(A, B):
    m, k, n = len(A), len(B), len(B[0])
    return [[sum((A[i][l] * B[l][j] for l in range(k)), Q(0)) for j in range(n)] for i in range(m)]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_scale(c, A):
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_T(A):
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def mat_vec(A, v):
    return [sum((A[i][j] * v[j] for j in range(len(v))), Q(0)) for i in range(len(A))]


def dot(u, v):
    return sum((u[i] * v[i] for i in range(len(u))), Q(0))


def outer(u, v):
    return [[u[i] * v[j] for j in range(len(v))] for i in range(len(u))]


def frob2(A):
    return sum((A[i][j] * A[i][j] for i in range(len(A)) for j in range(len(A[0]))), Q(0))


def det(A):
    M = [list(r) for r in A]
    n = len(M)
    d = Q(1)
    for c in range(n):
        p = None
        for r in range(c, n):
            if M[r][c] != 0:
                p = r
                break
        if p is None:
            return Q(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f != 0:
                for k in range(c, n):
                    M[r][k] -= f * M[c][k]
    return d


def mat_inv(A):
    n = len(A)
    M = [list(A[i]) + identity(n)[i] for i in range(n)]
    for c in range(n):
        p = None
        for r in range(c, n):
            if M[r][c] != 0:
                p = r
                break
        if p is None:
            raise ZeroDivisionError("singular matrix")
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [v / piv for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [M[r][k] - f * M[c][k] for k in range(2 * n)]
    return [row[n:] for row in M]


def cayley(rng, n, den=4, span=2):
    """Rational orthogonal matrix (I - S)(I + S)^{-1}, S skew-symmetric; orthogonality verified exactly."""
    if n == 1:
        return [[Q(1)]]
    S = [[Q(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            v = rng.rational(-span, span, den)
            S[i][j] = v
            S[j][i] = -v
    I = identity(n)
    Qm = mat_mul(mat_sub(I, S), mat_inv(mat_add(I, S)))
    if mat_mul(mat_T(Qm), Qm) != I:
        raise ArithmeticError("Cayley transform not orthogonal")
    return Qm


def F_diag(d, x):
    """F for a diagonal matrix diag(d) + x X, X = diag(1..n): sum_j j lambda_j, exact."""
    lam = sorted(Q(d[i]) + Q(x) * (i + 1) for i in range(len(d)))
    return sum(((j + 1) * lam[j] for j in range(len(lam))), Q(0))


def S_c(F, t, h):
    """Centered slope variation (13)."""
    return (F(t + h) - 2 * F(t) + F(t - h)) / Q(h)


def S_e(F, theta, t, h):
    """Endpoint slope variation (33)."""
    a = (1 - 2 * theta) * h
    return (F(t + h) - F(t + a) - F(t - a) + F(t - h)) / (2 * theta * h)


def tri_w(t, h, x):
    """Triangular weight w_{t,h}(x) = (1 - |x - t|/h)_+ (proof of Lemma 4.1)."""
    return max(1 - abs(Q(x) - t) / h, Q(0))


class PL:
    """Convex piecewise-linear F(x) = b + m x + sum a_i |x - c_i| with a_i >= 0."""

    def __init__(self, m, b, kinks):
        self.m, self.b, self.kinks = Q(m), Q(b), [(Q(c), Q(a)) for c, a in kinks]
        for _, a in self.kinks:
            if a < 0:
                raise ValueError("negative kink weight")

    def __call__(self, x):
        x = Q(x)
        return self.b + self.m * x + sum((a * abs(x - c) for c, a in self.kinks), Q(0))


def random_pl(rng, lo_slope, hi_slope, centre, spread, nk, den=1 << 12):
    """Random convex PL function whose slopes lie in [lo_slope, hi_slope]."""
    amax = (hi_slope - lo_slope) / 2
    w = [rng.integer(0, 8) for _ in range(nk)]
    tot = sum(w)
    scale = rng.rational(0, 1, 16)
    kinks = []
    for i in range(nk):
        c = centre + rng.rational(-1, 1, den) * spread
        a = amax * scale * Q(w[i], tot) if tot else Q(0)
        kinks.append((c, a))
    return PL((lo_slope + hi_slope) / 2, rng.rational(-1, 1, 16), kinks)


def sturm_count(a, c, x):
    """Number of eigenvalues < x of the symmetric tridiagonal matrix with diagonal a and squared
    off-diagonal moduli c (Sylvester inertia of the LDL^T factorization); None on a zero pivot."""
    cnt = 0
    d = None
    for i in range(len(a)):
        if i == 0 or c[i - 1] == 0:
            d = a[i] - x
        else:
            d = a[i] - x - c[i - 1] / d
        if d == 0:
            return None
        if d < 0:
            cnt += 1
    return cnt


def eig_brackets(a, c, bits=80):
    """Exact rational brackets [lo_j, hi_j] (width 2^-bits) of all eigenvalues, ascending."""
    n = len(a)
    bound = max(abs(a[i]) + (sqrt_bracket(c[i - 1], 8)[1] if i > 0 else 0)
                + (sqrt_bracket(c[i], 8)[1] if i < n - 1 else 0) for i in range(n)) + 1
    if sturm_count(a, c, -bound) != 0 or sturm_count(a, c, bound) != n:
        raise ArithmeticError("Gershgorin enclosure failed")
    out = []
    eps = Q(1, 1 << bits)
    for j in range(n):
        lo, hi = -bound, bound
        while hi - lo > eps:
            mid = (lo + hi) / 2
            cm = sturm_count(a, c, mid)
            k = 0
            while cm is None:
                k += 1
                mid = (lo + hi) / 2 + (hi - lo) * Q(1, 1 << (k + 4))
                cm = sturm_count(a, c, mid)
            if cm >= j + 1:
                hi = mid
            else:
                lo = mid
        out.append((lo, hi))
    return out


# ---------------------------------------------------------------- symbolic monomials

def _factor(m):
    f = {}
    p = 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


class Mono:
    """sign * prod base^exp, bases are primes (int) or variable names (str), exponents rational.
    Used to check the symbolic reductions (powers of n, delta, h, gamma, K and constants such as sqrt 2)."""

    def __init__(self, c=1, **v):
        c = Q(c)
        if c == 0:
            raise ValueError("zero monomial")
        self.sign = 1 if c > 0 else -1
        e = {}
        for p, k in _factor(abs(c.numerator)).items():
            e[p] = e.get(p, Q(0)) + k
        for p, k in _factor(c.denominator).items():
            e[p] = e.get(p, Q(0)) - k
        for name, k in v.items():
            e[name] = e.get(name, Q(0)) + Q(k)
        self.e = {b: k for b, k in e.items() if k != 0}

    @staticmethod
    def _make(sign, e):
        m = Mono.__new__(Mono)
        m.sign = sign
        m.e = {b: k for b, k in e.items() if k != 0}
        return m

    def __mul__(self, o):
        o = o if isinstance(o, Mono) else Mono(o)
        e = dict(self.e)
        for b, k in o.e.items():
            e[b] = e.get(b, Q(0)) + k
        return Mono._make(self.sign * o.sign, e)

    __rmul__ = __mul__

    def __pow__(self, q):
        q = Q(q)
        if self.sign < 0 and q.denominator != 1:
            raise ValueError("fractional power of a negative monomial")
        sign = -1 if (self.sign < 0 and q.numerator % 2 == 1) else 1
        return Mono._make(sign, {b: k * q for b, k in self.e.items()})

    def __truediv__(self, o):
        o = o if isinstance(o, Mono) else Mono(o)
        return self * (o ** -1)

    def __rtruediv__(self, o):
        return Mono(o) * (self ** -1)

    def same(self, o):
        o = o if isinstance(o, Mono) else Mono(o)
        return self.sign == o.sign and self.e == o.e


def sym(name):
    return Mono(1, **{name: 1})


def msqrt(m):
    return m ** HALF


# ---------------------------------------------------------------- reporting

class Family:
    def __init__(self, fid, title):
        self.fid, self.title = fid, title
        self.checks = 0
        self.fails = []
        self.controls = []
        self.scope = []

    def ok(self, cond, what):
        if cond is True:
            self.checks += 1
        else:
            self.fails.append(what)

    def control(self, cid, desc, accepted):
        full = self.fid + "." + cid
        if accepted is False:
            self.controls.append((full, desc))
        elif accepted is True:
            self.fails.append("negative control " + full + " was accepted: " + desc)
        else:
            self.fails.append("negative control " + full + " returned a non-boolean: " + desc)

    def note(self, s):
        self.scope.append(s)


# ================================================================ C01

def fam_c01(F):
    """Lemma 2.1, (8)-(10); the bound S_h(t) < n^3 used in the proofs of Theorems 4.1 and 4.2."""
    rng = Rng("C01")
    # (9): sum_j j * 1 = n(n+1)/2 and sum_j j * n = n^2(n+1)/2 (proof of Lemma 2.1: I <= X <= nI).
    for n in range(1, 201):
        F.ok(EQ(sum(range(1, n + 1)), fdiv(n * (n + 1), 2)), "sum j, n=%d" % n)
        F.ok(EQ(sum(j * n for j in range(1, n + 1)), fdiv(n * n * (n + 1), 2)), "sum j n, n=%d" % n)
    # Proofs of Theorems 4.1/4.2: S_h(t) <= max secant - min secant = (n^3 - n)/2 < n^3.
    for n in range(1, N_MAX + 1):
        width = fdiv(n * n * (n + 1), 2) - fdiv(n * (n + 1), 2)
        F.ok(EQ(width, fdiv(n ** 3 - n, 2)) and LT(width, n ** 3), "secant width < n^3, n=%d" % n)
    F.note("(9) slope width (n^3-n)/2 < n^3: n = 1..%d (finite cross-check of a statement universal in n)" % N_MAX)

    # (8) and (10) on exact sorted spectra.
    def ident(lam, trace_coef):
        n = len(lam)
        lhs = sum(((j + 1) * lam[j] for j in range(n)), Q(0))
        tail = sum(lam, Q(0)) + sum((sum(lam[l] for l in range(j, n)) for j in range(1, n)), Q(0))
        pair = trace_coef(n) * sum(lam, Q(0)) + HALF * sum(
            (lam[j] - lam[i] for i in range(n) for j in range(i + 1, n)), Q(0))
        return EQ(lhs, tail) and EQ(lhs, pair)

    spectra = []
    for n in range(1, 10):
        for _ in range(12):
            spectra.append(sorted(rng.rational(-2, 2, 97) for _ in range(n)))
    spectra.append([Q(1), Q(1), Q(2)])
    for lam in spectra:
        F.ok(ident(lam, lambda n: Q(n + 1, 2)), "(8)/(10) identity")
    F.control("N1", "(8) with trace coefficient n/2 instead of (n+1)/2",
              ALL(ident(lam, lambda n: Q(n, 2)) for lam in spectra))

    # Lemma 2.1 on exact diagonal T (||T|| <= 1): secant bounds (9), convexity, 0 <= S_h(t) <= (n^3-n)/2.
    def secant_ok(d, u, v, lower, upper):
        s = (F_diag(d, v) - F_diag(d, u)) / (v - u)
        return LE(lower, s) and LE(s, upper)

    probes = []
    for _ in range(400):
        n = rng.integer(1, 8)
        d = [rng.rational(-1, 1, 64) for _ in range(n)]
        u = rng.rational(-3, 3, 128)
        v = u + rng.rational(Q(1, 128), 3, 128)
        t = rng.rational(-3, 3, 128)
        h = rng.rational(Q(1, 256), 2, 256)
        probes.append((n, d, u, v, t, h))
        F.ok(secant_ok(d, u, v, fdiv(n * (n + 1), 2), fdiv(n * n * (n + 1), 2)), "(9) secant bounds")
        F.ok(LE(F_diag(d, (u + v) / 2), (F_diag(d, u) + F_diag(d, v)) / 2), "midpoint convexity")
        s = S_c(lambda x: F_diag(d, x), t, h)
        F.ok(LE(0, s) and LE(s, fdiv(n ** 3 - n, 2)) and LT(s, n ** 3), "0 <= S_h(t) <= (n^3-n)/2")
    F.note("(9), convexity and S_h bounds on 400 exact diagonal instances, n = 1..8")
    # Control: for t >= 2 the ordering of the branches d_i + t i is fixed and the slope equals sum j^2.
    d = [Q(1), Q(-1), Q(1, 2), Q(0)]
    sq = sum(j * j for j in range(1, 5))
    F.ok(EQ((F_diag(d, 4) - F_diag(d, 3)), Q(sq)), "slope sum j^2 for large t")
    F.control("N2", "upper secant bound replaced by sum j^2 - 1 (below the slope of F for large t)",
              secant_ok(d, Q(3), Q(4), Q(10), Q(sq - 1)))


# ================================================================ C02

def fam_c02(F):
    """Examples 2.2, 2.3, 3.1, 3.2 and 4.1: exactly checkable claims."""
    tenth = Q(1, 10)
    d22 = [tenth, Q(0)]
    f22 = lambda x: F_diag(d22, x)
    grid = [Q(k, 200) for k in range(-100, 141)]
    for t in grid:
        F.ok(EQ(f22(t), Q(3, 20) + Q(9, 2) * t + HALF * abs(t - tenth)), "(16) closed form")
        F.ok(EQ(f22(t), Q(1, 5) + 4 * t) if t <= tenth else EQ(f22(t), tenth + 5 * t), "(16) pieces")

    def s22_ok(scale):
        good = True
        for t in grid[::4]:
            for h in (Q(1, 25), Q(1, 100), Q(3, 50), Q(1, 7)):
                good = good and EQ(S_c(f22, t, h), max(1 - abs(t - tenth) / (scale * h), Q(0)))
        return good

    F.ok(s22_ok(Q(1)), "(17) triangular peak")
    F.control("N1", "(17) with 1/h replaced by 1/(2h)", s22_ok(Q(2)))
    # Example 4.1: window [0.06, 0.14], centre 0.1, h = 0.04; children [0.08,0.10], [0.10,0.12].
    F.ok(EQ(S_c(f22, tenth, Q(1, 25)), 1), "Example 4.1 S_0.04(0.1) = 1")
    F.ok(EQ(S_c(f22, Q(9, 100), Q(1, 100)), 0) and EQ(S_c(f22, Q(11, 100), Q(1, 100)), 0),
         "Example 4.1 child variations vanish")
    t, h = tenth, Q(1, 25)
    F.ok(EQ(t - h, Q(6, 100)) and EQ(t + h, Q(14, 100)) and EQ(t - h / 2, Q(8, 100)) and EQ(t + h / 2, Q(12, 100))
         and EQ(h / 4, Q(1, 100)), "Example 4.1 window arithmetic")
    # Example 2.3: crossings of the branches 0.16 + t, 0.10 + 2t, 3t.
    br = [Q(16, 100), Q(10, 100), Q(0)]
    cross = sorted((br[i] - br[j]) / ((j + 1) - (i + 1)) for i in range(3) for j in range(i + 1, 3))
    F.ok(cross == [Q(6, 100), Q(8, 100), Q(10, 100)], "Example 2.3 crossing points 0.06, 0.08, 0.10")
    # Example 2.3 (Figure 2 caption): S_0.006(0.08) ~ 1.8541, bracketed exactly by Sturm bisection.
    beta = Q(3, 1000)

    def F_br(s):
        a = [br[i] + s * (i + 1) for i in range(3)]
        b = eig_brackets(a, [beta * beta] * 2, bits=90)
        return (sum(((j + 1) * b[j][0] for j in range(3)), Q(0)), sum(((j + 1) * b[j][1] for j in range(3)), Q(0)))

    t, h = Q(8, 100), Q(6, 1000)
    fp, f0, fm = F_br(t + h), F_br(t), F_br(t - h)
    s_lo = (fp[0] - 2 * f0[1] + fm[0]) / h
    s_hi = (fp[1] - 2 * f0[0] + fm[1]) / h

    def rounds_to(v, lo, hi):
        return LE(v - Q(5, 100000), lo) and LT(hi, v + Q(5, 100000))

    F.ok(rounds_to(Q(18541, 10000), s_lo, s_hi), "Example 2.3: S_0.006(0.08) rounds to 1.8541")
    F.note("Example 2.3: exact bracket S_0.006(0.08) in [%s, %s] (6 decimals, truncated)"
           % (_dec(s_lo, 6), _dec(s_hi, 6)))
    F.control("N2", "Example 2.3 value 1.8641 instead of 1.8541", rounds_to(Q(18641, 10000), s_lo, s_hi))
    # Example 3.1: ||H||_2 < 1 (row sums), nonzero couplings, two eigenvalues within gamma = 1e-5.
    g = Q(1, 100000)
    dd = [Q(1, 4) - g / 2, HALF - g / 2, Q(1, 4) - g / 2, HALF, HALF, g / 2, g / 2, g / 2]
    bb = [Q(-1, 4), Q(-1, 4), Q(5, 10000), Q(1, 10), Q(5, 10000), Q(1, 4), Q(1, 4)]
    rows = [abs(dd[i]) + (abs(bb[i - 1]) if i > 0 else 0) + (abs(bb[i]) if i < 7 else 0) for i in range(8)]
    F.ok(LT(max(rows), 1), "Example 3.1 max row sum < 1 (so ||H||_2 < 1)")
    F.ok(ALL(b != 0 for b in bb), "Example 3.1 couplings nonzero")
    eb = eig_brackets(dd, [b * b for b in bb], bits=80)
    unit = Q(1, 10 ** 12)
    lam_q, mu_q = Q(-5173792, 10 ** 12), Q(4739763, 10 ** 12)

    def near(v):
        return [j for j in range(8) if LE(v - unit, eb[j][0]) and LE(eb[j][1], v + unit)]

    jl, jm = near(lam_q), near(mu_q)
    F.ok(len(jl) == 1 and len(jm) == 1 and jm[0] == jl[0] + 1,
         "Example 3.1: eigenvalues -5.173792e-6 and 4.739763e-6 (to 1e-12), adjacent")
    if len(jl) == 1 and len(jm) == 1:
        F.ok(LT(eb[jm[0]][1] - eb[jl[0]][0], g), "Example 3.1: |lambda - mu| < gamma")
    F.control("N3", "Example 3.1 eigenvalue -5.173892e-6 (changed digit)", len(near(Q(-5173892, 10 ** 12))) == 1)
    # Example 3.2: tau = 4 sqrt(n gamma) ~ 0.0358 for n = 8; the stated L_k versus tau.
    tau2 = 16 * 8 * g
    F.ok(LE(Q(3575, 100000) ** 2, tau2) and LT(tau2, Q(3585, 100000) ** 2), "Example 3.2: tau rounds to 0.0358")
    Lk = [Q(1443, 10000), Q(1443, 10000), Q(289, 1000000), Q(746, 10 ** 7), Q(354, 10 ** 6), Q(1768, 10000),
          Q(1768, 10000)]
    yes = [False, False, True, True, True, False, False]
    F.ok(ALL((LE(Lk[k] * Lk[k], tau2) is yes[k]) for k in range(7)), "Example 3.2 table: L_k <= tau column")


def _dec(v, places):
    v = Q(v)
    s = "-" if v < 0 else ""
    v = abs(v)
    ip = v.numerator // v.denominator
    fp = ((v - ip) * 10 ** places).numerator // ((v - ip) * 10 ** places).denominator
    return "%s%d.%0*d" % (s, ip, places, fp)


# ================================================================ C03

def proj_gap_sq(a, b):
    """-det(Pi_a - Pi_b) = ||Pi_a - Pi_b||_2^2 for the traceless symmetric 2x2 difference of projectors."""
    na, nb = a[0] ** 2 + a[1] ** 2, b[0] ** 2 + b[1] ** 2
    P = [[a[0] * a[0] / na - b[0] * b[0] / nb, a[0] * a[1] / na - b[0] * b[1] / nb],
         [a[1] * a[0] / na - b[1] * b[0] / nb, a[1] * a[1] / na - b[1] * b[1] / nb]]
    if P[0][0] + P[1][1] != 0 or P[0][1] != P[1][0]:
        raise ArithmeticError("projector difference not traceless symmetric")
    return -(P[0][0] * P[1][1] - P[0][1] * P[1][0])


def fam_c03(F):
    """Lemma 3.1, Step 1 and (21): the constants 1/4, 3/4, 2, 3/8 and sqrt(3/8) > 1/2."""
    rng = Rng("C03")
    n = sym("n")
    F.ok((n * (Mono(1) / (2 * msqrt(n))) ** 2).same(Q(1, 4)), "n (1/(2 sqrt n))^2 = 1/4")
    F.ok(EQ(1 - Q(1, 4), Q(3, 4)) and EQ(Q(3, 4) / 2, Q(3, 8)), "1 - 1/4 = 3/4 and (3/4)/2 = 3/8")
    F.ok(GT(Q(3, 8), Q(1, 4)) and GT(sqrt_bracket(Q(3, 8))[0], HALF), "sqrt(3/8) > 1/2")
    F.control("N1", "threshold 1/sqrt(n) instead of 1/(2 sqrt n): discarded mass n (1/sqrt n)^2 <= 1/4",
              (n * (Mono(1) / msqrt(n)) ** 2).same(Q(1, 4)))
    F.control("N2", "ratio 1/4 instead of 3/8: sqrt(1/4) > 1/2", GT(Q(1, 4), Q(1, 4)))

    # ||Pi_a - Pi_b||_2 = |det(a, b)| / (|a| |b|), squared, on random rational rows.
    pairs = []
    for _ in range(300):
        a = (rng.nonzero(-3, 3, 7), rng.rational(-3, 3, 7))
        b = (rng.rational(-3, 3, 5), rng.nonzero(-3, 3, 5))
        pairs.append((a, b))
        dt = a[0] * b[1] - a[1] * b[0]
        F.ok(EQ(proj_gap_sq(a, b), dt * dt / ((a[0] ** 2 + a[1] ** 2) * (b[0] ** 2 + b[1] ** 2))),
             "projector-gap identity")
    F.control("N3", "projector-gap identity with the dot product in place of the determinant",
              ALL(EQ(proj_gap_sq(a, b), (a[0] * b[0] + a[1] * b[1]) ** 2
                     / ((a[0] ** 2 + a[1] ** 2) * (b[0] ** 2 + b[1] ** 2))) for a, b in pairs))

    # Step 1 on exact data: rows of an n x 2 matrix with orthonormal rational columns (Cayley transform).
    count = 0
    for nn in range(2, 10):
        for _ in range(6):
            Om = cayley(rng, nn)
            rows = [(Om[i][0], Om[i][1]) for i in range(nn)]
            G = [[sum((r[a] * r[b] for r in rows), Q(0)) for b in range(2)] for a in range(2)]
            F.ok(G == [[1, 0], [0, 1]], "sum r_i^T r_i = I_2")
            thr = Q(1, 4 * nn)
            J = [i for i in range(nn) if GE(rows[i][0] ** 2 + rows[i][1] ** 2, thr)]
            disc = sum((rows[i][0] ** 2 + rows[i][1] ** 2 for i in range(nn) if i not in J), Q(0))
            F.ok(LE(disc, Q(1, 4)), "discarded rows have squared norm at most 1/4")
            M = [[sum((rows[i][a] * rows[i][b] for i in J), Q(0)) - (Q(3, 4) if a == b else 0) for b in range(2)]
                 for a in range(2)]
            F.ok(GE(M[0][0], 0) and GE(M[1][1], 0) and GE(M[0][0] * M[1][1] - M[0][1] ** 2, 0),
                 "sum over J >= (3/4) I_2")
            F.ok(LE(sum((rows[i][0] ** 2 + rows[i][1] ** 2 for i in J), Q(0)), 2), "sum over J of norms <= 2")
            for p in J:
                rp = rows[p]
                e = (-rp[1], rp[0])
                e2 = e[0] ** 2 + e[1] ** 2
                tot = sum(((rows[i][0] * e[0] + rows[i][1] * e[1]) ** 2 for i in J), Q(0))
                F.ok(GE(tot, Q(3, 4) * e2), "sum_J |r_i e|^2 >= 3/4")
                qs = [q for q in J if GE((rows[q][0] * e[0] + rows[q][1] * e[1]) ** 2,
                                         Q(3, 8) * (rows[q][0] ** 2 + rows[q][1] ** 2) * e2)]
                F.ok(len(qs) > 0 and p not in qs, "a row q != p with ratio >= 3/8 exists")
                if qs:
                    F.ok(GE(proj_gap_sq(rp, rows[qs[0]]), Q(3, 8)), "(21) ||Pi_p - Pi_q||^2 >= 3/8")
                count += 1
    F.note("Step 1 on 48 exact orthonormal pairs (Cayley transforms), n = 2..9, %d choices of p" % count)


# ================================================================ C04

def tri_apply(dg, beta, u):
    n = len(dg)
    return [dg[i] * u[i] + (beta[i - 1] * u[i - 1] if i > 0 else 0) + (beta[i] * u[i + 1] if i < n - 1 else 0)
            for i in range(n)]


def wronskian_ok(dg, beta, u1, u2, sign):
    """(22) in the general form beta_i det(r_i; r_{i+1}) = sum_{j<=i} [(H u2)_j (u1)_j - (H u1)_j (u2)_j]."""
    n = len(dg)
    h1, h2 = tri_apply(dg, beta, u1), tri_apply(dg, beta, u2)
    acc = Q(0)
    for i in range(n):
        acc += h2[i] * u1[i] - h1[i] * u2[i]
        lhs = beta[i] * (u1[i] * u2[i + 1] - u1[i + 1] * u2[i]) if i < n - 1 else Q(0)
        if not EQ(lhs, sign * acc):
            return False
    return True


def fam_c04(F):
    """Lemma 3.1, Step 2: the discrete Wronskian identity (22) and |sum_{j<=i} (u1)_j (u2)_j| <= 1/2."""
    rng = Rng("C04")
    data = []
    for n in range(2, 10):
        for _ in range(10):
            dg = [rng.rational(-1, 1, 16) for _ in range(n)]
            beta = [rng.rational(-1, 1, 16) for _ in range(n - 1)]
            u1 = [rng.rational(-2, 2, 9) for _ in range(n)]
            u2 = [rng.rational(-2, 2, 9) for _ in range(n)]
            data.append((dg, beta, u1, u2))
            F.ok(wronskian_ok(dg, beta, u1, u2, 1), "(22) general telescoping form")
    F.control("N1", "(22) with the sign of the right-hand side reversed",
              ALL(wronskian_ok(dg, beta, u1, u2, -1) for dg, beta, u1, u2 in data))
    # Exact eigenpairs: block-diagonal tridiagonal matrices with Pythagorean 2x2 blocks
    # [[m+3s, 4s], [4s, m-3s]] (eigenvectors (2,1), (1,-2), eigenvalues m+5s, m-5s) and 1x1 blocks.
    for _ in range(40):
        dg, beta, vecs = [], [], []
        while len(dg) < 7:
            if len(dg) > 0:
                beta.append(Q(0))
            if rng.below(3) == 0:
                m = rng.rational(-1, 1, 8)
                pos = len(dg)
                dg.append(m)
                vecs.append((pos, [Q(1)], m))
            else:
                m, s = rng.rational(-1, 1, 8), rng.nonzero(-Q(1, 4), Q(1, 4), 16)
                pos = len(dg)
                dg += [m + 3 * s, m - 3 * s]
                beta.append(4 * s)
                vecs.append((pos, [Q(2), Q(1)], m + 5 * s))
                vecs.append((pos, [Q(1), Q(-2)], m - 5 * s))
        n = len(dg)
        full = []
        for pos, v, lam in vecs:
            u = [Q(0)] * n
            for k, x in enumerate(v):
                u[pos + k] = x
            F.ok(tri_apply(dg, beta, u) == [lam * x for x in u], "exact eigenpair")
            full.append((u, lam))
        for a in range(len(full)):
            for b in range(len(full)):
                (u1, lam), (u2, mu) = full[a], full[b]
                good = True
                acc = Q(0)
                for i in range(n - 1):
                    acc += u1[i] * u2[i]
                    good = good and EQ(beta[i] * (u1[i] * u2[i + 1] - u1[i + 1] * u2[i]), (mu - lam) * acc)
                F.ok(good, "(22) for exact eigenpairs")
    # |sum_{j<=i} (u1)_j (u2)_j| = |u1^T (P_{<=i} - I/2) u2| <= 1/2 for orthonormal u1, u2.
    for n in range(2, 10):
        for _ in range(8):
            Om = cayley(rng, n)
            u1 = [Om[i][0] for i in range(n)]
            u2 = [Om[i][1] for i in range(n)]
            F.ok(EQ(dot(u1, u2), 0) and EQ(dot(u1, u1), 1) and EQ(dot(u2, u2), 1), "orthonormal pair")
            for i in range(1, n + 1):
                s = sum((u1[j] * u2[j] for j in range(i)), Q(0))
                s2 = sum((u1[j] * u2[j] * (HALF if j < i else -HALF) for j in range(n)), Q(0))
                F.ok(EQ(s, s2) and LE(abs(s), HALF), "|sum_{j<=i} u1_j u2_j| <= 1/2")
    # The constant 1/2 is attained in the limit; the explicit pair (3/5, 4/5), (4/5, -3/5) gives 12/25.
    u1, u2 = [Q(3, 5), Q(4, 5)], [Q(4, 5), Q(-3, 5)]
    F.ok(EQ(abs(u1[0] * u2[0]), Q(12, 25)) and LE(Q(12, 25), HALF), "explicit pair, 12/25 <= 1/2")
    F.control("N2", "bound 1/4 instead of 1/2 for |sum_{j<=i} u1_j u2_j|", LE(abs(u1[0] * u2[0]), Q(1, 4)))
    g = sym("gamma")
    F.ok((g * HALF).same(g / 2), "|beta_i| |det| <= |mu - lambda| / 2 <= gamma / 2")
    F.note("(22) on 80 random tridiagonal data sets (n = 2..9) and on exact eigenpairs of 40 block matrices (n = 7, 8)")


# ================================================================ C05

def fam_c05(F):
    """Lemma 3.1, Step 3: tau = 4 sqrt(n gamma), cases (a)-(c) and the path bound 5/16 < 1/2."""
    rng = Rng("C05")
    nn, g = sym("n"), sym("gamma")
    tau = 4 * msqrt(nn * g)
    F.ok((5 * g / tau ** 2).same(Q(5, 16) / nn), "5 gamma / tau^2 = 5/(16 n)")
    F.ok((tau ** 2).same(16 * nn * g), "tau^2 = 16 n gamma")
    gmax = Q(1, 256) / nn ** 2
    F.ok((4 * msqrt(nn * gmax)).same(Mono(1) / (4 * msqrt(nn))), "tau = 1/(4 sqrt n) at gamma = 1/(256 n^2)")
    for n in range(2, N_MAX + 1):
        F.ok(LT(Q(n - 1) * Q(5, 16 * n), Q(5, 16)) and LT(Q(5, 16), HALF), "(n-1) 5/(16n) < 5/16 < 1/2")
    F.note("path bound (n-1) 5/(16n) < 5/16 < 1/2: n = 2..%d (finite cross-check)" % N_MAX)
    F.control("N1", "tau = 2 sqrt(n gamma): (n-1) 5 gamma / tau^2 = 5(n-1)/(4n) < 1/2 at n = 2",
              LT(Q(1) * Q(5, 4 * 2), HALF))
    F.control("N2", "path of n^2 steps instead of at most n - 1: n^2 * 5/(16 n) < 1/2 at n = 2",
              LT(Q(4) * Q(5, 32), HALF))
    # Squared forms at sample (n, gamma) with 0 < gamma <= 1/(256 n^2).
    samples = []
    for n in list(range(2, 41)) + [100, 1000, N_MAX]:
        for u in (Q(1), HALF, Q(1, 3), Q(1, 1000)):
            samples.append((n, u * Q(1, 256 * n * n)))
    for n, gm in samples:
        t2 = 16 * n * gm
        F.ok(LE(t2, Q(1, 16 * n)), "tau <= 1/(4 sqrt n)")
        F.ok(GT(Q(1, 4 * n), t2), "endpoint rows large: (1/(2 sqrt n))^2 > tau^2")
        F.ok(LE(t2, 1), "tau <= 1")
        F.ok(LE(gm / (2 * t2), 5 * gm / t2), "case (a): gamma/(2 tau^2) <= 5 gamma/tau^2")
        F.ok(LE(t2, 6) and LE(gm / 2, 3 * gm / t2), "case (c): gamma/2 <= 3 gamma/tau^2")
        F.ok(LE(t2, Q(1, 16 * n)), "tau^2 = 16 n gamma <= 1/(16 n)")

    # Case (c), scalar chain: |b1| r1 > tau, |b2| r3 > tau, r2 <= tau imply
    # 2 gamma/(|b1 b2| r1 r3) + gamma r2/(2 |b2| r3) <= 5 gamma/tau^2.  All comparisons squared (rational).
    def chain_c(n, gm, b1, b2, r1, r2, r3, bound_coef):
        t2 = 16 * n * gm
        if not (GT(b1 * b1 * r1 * r1, t2) and GT(b2 * b2 * r3 * r3, t2) and LE(r2 * r2, t2)):
            raise ValueError("hypotheses of case (c) violated")
        T1 = 2 * gm / (abs(b1 * b2) * r1 * r3)
        T2 = gm * r2 / (2 * abs(b2) * r3)
        return LT(T1, 2 * gm / t2) and LT(T2, gm / 2) and LE(T1 + T2, bound_coef * gm / t2)

    for _ in range(3000):
        n = rng.integer(2, 64)
        gm = rng.rational(Q(1, 1000), 1, 1000) * Q(1, 256 * n * n)
        t2 = 16 * n * gm
        lo_t, hi_t = sqrt_bracket(t2, 64)
        b1, b2 = rng.nonzero(-1, 1, 64), rng.nonzero(-1, 1, 64)
        r1 = hi_t / abs(b1) * (1 + rng.rational(Q(1, 1000), 3, 1000))
        r3 = hi_t / abs(b2) * (1 + rng.rational(Q(1, 1000), 3, 1000))
        r2 = lo_t * rng.rational(0, 1, 1000)
        F.ok(chain_c(n, gm, b1, b2, r1, r2, r3, 5), "case (c) chain")
    n, gm = 4, Q(1, 4096 * 4)
    t2 = 16 * n * gm
    lo_t, hi_t = sqrt_bracket(t2, 64)
    F.ok(EQ(lo_t * lo_t, t2), "tau rational in the boundary instance")
    tiny = 1 + Q(1, 10 ** 9)
    worst = (n, gm, Q(1), Q(1), lo_t * tiny, lo_t, lo_t * tiny)
    F.ok(chain_c(*worst, 5), "case (c) chain, near-extremal instance")
    F.control("N3", "case (c) bound 2 gamma/tau^2 (second term dropped), near-extremal instance",
              chain_c(*worst[:7], 2))

    # Case (c), determinant step: with r_{i+1} given by the three-term recurrence,
    # |det(r_{i-1}, r_{i+1})|/(|r_{i-1}||r_{i+1}|) <= 2 gamma/(|b1 b2| |r_{i-1}||r_{i+1}|) + gamma |r_i|/(2 |b2| |r_{i+1}|).
    def det2(a, b):
        return a[0] * b[1] - a[1] * b[0]

    done = 0
    for _ in range(600):
        rp = (rng.rational(-1, 1, 32), rng.rational(-1, 1, 32))
        ri = (rp[0] + rng.rational(-Q(1, 64), Q(1, 64), 512), rp[1] + rng.rational(-Q(1, 64), Q(1, 64), 512))
        b1, b2 = rng.nonzero(-1, 1, 16), rng.nonzero(-1, 1, 16)
        dlt = rng.rational(-Q(1, 100), Q(1, 100), 1000)       # lambda - mu
        dmc = rng.rational(-4, 4, 16)                          # d_i - (lambda + mu)/2, |.| <= 4
        gm = max(abs(dlt), 2 * abs(b1 * det2(rp, ri)), Q(1, 10 ** 6))
        rD = (ri[0] * dlt / 2, -ri[1] * dlt / 2)
        rn = ((rD[0] - b1 * rp[0] - dmc * ri[0]) / b2, (rD[1] - b1 * rp[1] - dmc * ri[1]) / b2)
        n1, n2, n3 = rp[0] ** 2 + rp[1] ** 2, ri[0] ** 2 + ri[1] ** 2, rn[0] ** 2 + rn[1] ** 2
        if n1 == 0 or n3 == 0:
            continue
        # recurrence holds exactly
        F.ok(EQ(b1 * rp[0] + dmc * ri[0] + b2 * rn[0], ri[0] * dlt / 2)
             and EQ(b1 * rp[1] + dmc * ri[1] + b2 * rn[1], -ri[1] * dlt / 2), "three-term recurrence")
        l1, h1 = sqrt_bracket(n1)
        l2, h2 = sqrt_bracket(n2)
        l3, h3 = sqrt_bracket(n3)
        lhs_hi = abs(det2(rp, rn)) / (l1 * l3)
        rhs_lo = 2 * gm / (abs(b1 * b2) * h1 * h3) + gm * l2 / (2 * abs(b2) * h3)
        F.ok(LE(lhs_hi, rhs_lo), "case (c) determinant bound")
        done += 1
    F.note("case (c): 3000 sampled scalar chains (n = 2..64) and %d exact recurrence instances" % done)


# ================================================================ C06

def fam_c06(F):
    """Lemma 3.1, Step 4: residual of w_1, the commutator [H, P_L], 2 sqrt n (gamma/2 + sqrt 2 tau) <= 16 n sqrt gamma."""
    rng = Rng("C06")
    nn, g = sym("n"), sym("gamma")
    tau = 4 * msqrt(nn * g)
    F.ok((4 * msqrt(nn) * tau).same(16 * nn * msqrt(g)), "4 sqrt(n) tau = 16 n sqrt(gamma)")
    s2lo, s2hi = sqrt_bracket(2)
    F.ok(LT(Q(2), Q(9, 4)) and LT(s2hi, Q(3, 2)), "sqrt 2 < 3/2, hence 2 - sqrt 2 > 1/2")

    def step4(n, gm, coef_hi):
        # gamma/2 + coef tau <= 2 tau, i.e. 2 sqrt n (gamma/2 + coef tau) <= 4 sqrt n tau, with an upper
        # bracket coef_hi of the coefficient (the paper: coef = sqrt 2) and a bracket of tau = 4 sqrt(n gamma)
        t_lo, t_hi = sqrt_bracket(16 * n * gm)
        return LE(gm / 2 + coef_hi * t_hi, 2 * t_lo)

    pts = []
    for n in list(range(2, 41)) + [100, 1000, N_MAX]:
        for u in (Q(1), HALF, Q(1, 7), Q(1, 10 ** 6)):
            gm = u * Q(1, 256 * n * n)
            pts.append((n, gm))
            F.ok(step4(n, gm, s2hi), "Step 4 chain")
            F.ok(LE(gm * gm, 16 * n * gm), "gamma <= tau (reduction)")
    F.control("N1", "Step 4 with sqrt 2 tau replaced by 2 tau", ALL(step4(n, gm, Q(2)) for n, gm in pts))
    # Commutator: [H, P_L] w = beta_k w_k e_{k+1} - beta_k w_{k+1} e_k, and its norm <= sqrt 2 tau.
    data = []
    for n in range(2, 9):
        for _ in range(8):
            dg = [rng.rational(-1, 1, 8) for _ in range(n)]
            beta = [rng.rational(-1, 1, 8) for _ in range(n - 1)]
            w = [rng.rational(-1, 1, 8) for _ in range(n)]
            H = [[dg[i] if i == j else (beta[min(i, j)] if abs(i - j) == 1 else Q(0)) for j in range(n)]
                 for i in range(n)]
            for k in range(1, n):
                PL_ = [[Q(1) if (i == j and i < k) else Q(0) for j in range(n)] for i in range(n)]
                C = mat_sub(mat_mul(H, PL_), mat_mul(PL_, H))
                data.append((C, w, beta, k, n))
    for sgn in (1, -1):
        good = []
        for C, w, beta, k, n in data:
            Cw = mat_vec(C, w)
            exp = [Q(0)] * n
            exp[k] = sgn * beta[k - 1] * w[k - 1]
            exp[k - 1] = -sgn * beta[k - 1] * w[k]
            good.append(Cw == exp)
        if sgn == 1:
            for v in good:
                F.ok(v, "commutator boundary terms")
        else:
            F.control("N2", "commutator with the signs of both boundary terms reversed", ALL(good))
    for _ in range(500):
        b = rng.nonzero(-1, 1, 64)
        a1, a2 = rng.rational(-1, 1, 64), rng.rational(-1, 1, 64)
        t2 = b * b * max(a1 * a1, a2 * a2)
        F.ok(LE(b * b * (a1 * a1 + a2 * a2), 2 * t2), "|beta_k| (w_k^2 + w_{k+1}^2)^{1/2} <= sqrt 2 tau")
    # Residual of w_1: exact symmetric H = U diag(lam) U^T with rational orthogonal U (not tridiagonal; the
    # residual identity uses only the eigen-equations); w = (u1)_p u1 + (u2)_p u2 (unnormalized).
    for n in range(2, 8):
        for _ in range(4):
            U = cayley(rng, n)
            lam = [rng.rational(-1, 1, 16) for _ in range(n)]
            H = mat_mul(mat_mul(U, [[lam[i] if i == j else Q(0) for j in range(n)] for i in range(n)]), mat_T(U))
            u1 = [U[i][0] for i in range(n)]
            u2 = [U[i][1] for i in range(n)]
            c = (lam[0] + lam[1]) / 2
            for p in range(n):
                w = [u1[p] * u1[i] + u2[p] * u2[i] for i in range(n)]
                res = [x - c * y for x, y in zip(mat_vec(H, w), w)]
                rp2 = u1[p] ** 2 + u2[p] ** 2
                F.ok(EQ(dot(res, res), ((lam[0] - lam[1]) / 2) ** 2 * dot(w, w)) and EQ(dot(w, w), rp2),
                     "||(H - c) w_1|| = |lambda - mu|/2")
                F.ok(EQ(w[p], rp2), "(w_1)_p = ||r_p||")
                F.ok(ALL(LE(w[i] ** 2, (u1[i] ** 2 + u2[i] ** 2) * rp2) for i in range(n)), "|(w_1)_i| <= ||r_i||")
    # X-responses: v1 supported on 1..k, v2 on k+1..n give v1^T X v1 <= k < k+1 <= v2^T X v2.
    for _ in range(300):
        n = rng.integer(2, 10)
        k = rng.integer(1, n - 1)
        v1 = [rng.rational(-1, 1, 8) if i < k else Q(0) for i in range(n)]
        v2 = [rng.rational(-1, 1, 8) if i >= k else Q(0) for i in range(n)]
        v1[0] = v1[0] or Q(1)
        v2[n - 1] = v2[n - 1] or Q(1)
        x1 = sum(((i + 1) * v1[i] ** 2 for i in range(n)), Q(0))
        x2 = sum(((i + 1) * v2[i] ** 2 for i in range(n)), Q(0))
        F.ok(EQ(dot(v1, v2), 0) and LE(x1, k * dot(v1, v1)) and GE(x2, (k + 1) * dot(v2, v2)), "X-responses")
    e = lambda i, n: [Q(1) if j == i else Q(0) for j in range(n)]
    v1, v2 = e(2, 6), e(3, 6)
    resp = sum(((i + 1) * v2[i] ** 2 for i in range(6)), Q(0)) - sum(((i + 1) * v1[i] ** 2 for i in range(6)), Q(0))
    F.ok(GE(resp, 1), "v2^T X v2 - v1^T X v1 >= 1 for adjacent unit vectors")
    F.control("N3", "response gap >= 2 instead of >= 1 (adjacent unit vectors across the cut)", GE(resp, 2))


# ================================================================ C07

def fam_c07(F):
    """Lemma 3.2 and (26)-(27): H - H~ = AQ + QA - QAQ, the nuclear-norm bound 96 n sqrt(gamma), S^aux >= 1."""
    rng = Rng("C07")
    nn, g = sym("n"), sym("gamma")
    s2 = msqrt(Mono(2))
    per = 16 * nn * msqrt(g)
    F.ok(msqrt(2 * per ** 2).same(s2 * per), "(sum_{i=1,2} (16 n sqrt gamma)^2)^{1/2} = sqrt 2 * 16 n sqrt gamma")
    F.ok((3 * s2 * (s2 * per)).same(96 * nn * msqrt(g)), "3 sqrt2 * sqrt2 * 16 n sqrt gamma = 96 n sqrt gamma")
    F.control("N1", "the sqrt 2 of the two-term sum omitted: 3 sqrt 2 * 16 n sqrt gamma = 96 n sqrt gamma",
              (3 * s2 * per).same(96 * nn * msqrt(g)))
    insts = []
    for n in range(2, 7):
        for _ in range(5):
            k = rng.integer(1, n - 1)
            U1, U2 = cayley(rng, k), cayley(rng, n - k)
            v1 = [U1[i][0] if i < k else Q(0) for i in range(n)]
            v2 = [Q(0) if i < k else U2[i - k][0] for i in range(n)]
            dg = [rng.rational(-1, 1, 8) for _ in range(n)]
            beta = [rng.rational(-1, 1, 8) for _ in range(n - 1)]
            H = [[dg[i] if i == j else (beta[min(i, j)] if abs(i - j) == 1 else Q(0)) for j in range(n)]
                 for i in range(n)]
            c = rng.rational(-1, 1, 8)
            insts.append((n, v1, v2, H, c))

    def expansion_ok(inst, sgn):
        """H - H~ == AQ + QA + sgn QAQ (the paper: sgn = -1)."""
        n, v1, v2, H, c = inst
        I = identity(n)
        Qp = mat_add(outer(v1, v1), outer(v2, v2))
        Ht = mat_add(mat_mul(mat_mul(mat_sub(I, Qp), H), mat_sub(I, Qp)), mat_scale(c, Qp))
        A = mat_sub(H, mat_scale(c, I))
        AQ, QA = mat_mul(A, Qp), mat_mul(Qp, A)
        QAQ = mat_mul(Qp, AQ)
        return mat_sub(H, Ht) == mat_add(mat_add(AQ, QA), mat_scale(Q(sgn), QAQ))

    for inst in insts:
        n, v1, v2, H, c = inst
        I = identity(n)
        Qp = mat_add(outer(v1, v1), outer(v2, v2))
        F.ok(mat_mul(Qp, Qp) == Qp and Qp == mat_T(Qp) and EQ(sum((Qp[i][i] for i in range(n)), Q(0)), 2),
             "Q orthogonal projector of rank two")
        Ht = mat_add(mat_mul(mat_mul(mat_sub(I, Qp), H), mat_sub(I, Qp)), mat_scale(c, Qp))
        F.ok(mat_vec(Ht, v1) == [c * x for x in v1] and mat_vec(Ht, v2) == [c * x for x in v2] and Ht == mat_T(Ht),
             "(26) H~ v_i = c v_i, H~ symmetric")
        F.ok(expansion_ok(inst, -1), "H - H~ = AQ + QA - QAQ")
        A = mat_sub(H, mat_scale(c, I))
        AQ, QA = mat_mul(A, Qp), mat_mul(Qp, A)
        QAQ = mat_mul(Qp, AQ)
        Av1, Av2 = mat_vec(A, v1), mat_vec(A, v2)
        F.ok(EQ(frob2(AQ), dot(Av1, Av1) + dot(Av2, Av2)), "||AQ||_F^2 = sum ||A v_i||^2")
        F.ok(QA == mat_T(AQ) and LE(frob2(QAQ), frob2(AQ)), "QA = (AQ)^T, ||QAQ||_F <= ||AQ||_F")
        for M in (AQ, QAQ):
            G = mat_mul(mat_T(M), M)
            idx = range(n)
            e2 = sum((G[i][i] * G[j][j] - G[i][j] * G[j][i] for i in idx for j in idx if i < j), Q(0))
            e3 = sum((det([[G[a][b] for b in (i, j, l)] for a in (i, j, l)])
                      for i in idx for j in idx for l in idx if i < j < l), Q(0))
            # rank <= 2 (e3 = 0); nuclear^2 = F^2 + 2 sqrt(e2) <= 2 F^2  <=>  4 e2 <= F^4
            F.ok(EQ(e3, 0) and LE(4 * e2, frob2(M) ** 2), "rank <= 2 and ||M||_* <= sqrt 2 ||M||_F")
    F.control("N2", "expansion with +QAQ instead of -QAQ", ALL(expansion_ok(inst, 1) for inst in insts))
    # Nuclear <= 1 * Frobenius fails for a rank-two instance with two nonzero singular values.
    M = [[Q(1), Q(0)], [Q(0), Q(1)]]
    G = mat_mul(mat_T(M), M)
    e2 = G[0][0] * G[1][1] - G[0][1] ** 2
    F.control("N3", "nuclear-Frobenius factor 1 instead of sqrt 2 (rank-two identity)", LE(e2, Q(0)))
    # (27) via supporting slopes, exact on diagonal H~ with a repeated eigenvalue d_a = d_b (a <= k < b):
    # S^aux_h(t) >= v2^T X v2 - v1^T X v1 = b - a >= 1 for v1 = e_a, v2 = e_b.
    for _ in range(400):
        n = rng.integer(2, 8)
        a = rng.integer(1, n - 1)
        b = rng.integer(a + 1, n)
        d = [rng.rational(-1, 1, 32) for _ in range(n)]
        d[b - 1] = d[a - 1]
        h = rng.rational(Q(1, 512), 1, 512)
        Saux = (F_diag(d, h) + F_diag(d, -h) - 2 * F_diag(d, 0)) / h
        F.ok(GE(Saux, b - a) and GE(b - a, 1), "(27) S^aux_h >= response gap >= 1")


# ================================================================ C08

def prop31_lower(n, h, c_nuc, gden, coef):
    """Lower bound 1 - coef n N / h with N = c_nuc n sqrt(gamma), gamma = h^2/(gden n^4) (proof of Prop. 3.1)."""
    r = isqrt(gden)
    if r * r != gden:
        raise ValueError("gden not a square")
    gamma = Q(h) * h / (gden * n ** 4)
    sg = Q(h) / (r * n * n)
    if sg * sg != gamma or sg <= 0:
        raise ArithmeticError("sqrt(gamma) wrong")
    N = c_nuc * n * sg
    return gamma, sg, N, 1 - coef * n * N / h


def fam_c08(F):
    """Proposition 3.1 and (28): gamma = h^2/(2^20 n^4), the transfer coefficient 4, 1 - 384/1024 = 5/8 > 1/2."""
    rng = Rng("C08")
    c_nuc = 192 if FAULT[0] else 96
    nn, h, g = sym("n"), sym("h"), sym("gamma")
    sg = msqrt(h ** 2 / (Mono(2 ** 20) * nn ** 4))
    F.ok(sg.same(h / (Mono(2 ** 10) * nn ** 2)), "sqrt(h^2/(2^20 n^4)) = h/(2^10 n^2)")
    F.ok((4 * nn * (c_nuc * nn * sg) / h).same(Q(3, 8)), "(4n/h) 96 n sqrt(gamma) = 384/1024 = 3/8")
    F.ok(EQ(1 - Q(384, 1024), Q(5, 8)) and GT(Q(5, 8), HALF), "1 - 3/8 = 5/8 > 1/2")
    F.ok(EQ(1 + 1 + 2, 4), "transfer coefficient: |1| + |-2| + |1| = 4")
    for n in range(2, N_MAX + 1):
        gamma, _, _, low = prop31_lower(n, Q(1), c_nuc, 2 ** 20, 4)
        F.ok(LE(gamma, Q(1, 256 * n * n)) and EQ(low, Q(5, 8)), "h = 1: gamma <= 1/(256n^2), bound 5/8")
    F.note("h = 1 (largest admissible radius): n = 2..%d (finite cross-check)" % N_MAX)
    samples = []
    for _ in range(2000):
        n = rng.integer(2, 200)
        hh = rng.rational(Q(1, 10 ** 6), 1, 10 ** 6)
        samples.append((n, hh))
        gamma, sgv, N, low = prop31_lower(n, hh, c_nuc, 2 ** 20, 4)
        F.ok(GT(gamma, 0) and LE(gamma, Q(1, 256 * n * n)), "0 < h <= 1 gives 0 < gamma <= 1/(256 n^2)")
        F.ok(EQ(low, Q(5, 8)) and GT(low, HALF), "1 - 384 n^2 sqrt(gamma)/h = 5/8 > 1/2")
        # complete scalar chain: S^aux >= 1, N' <= N, |F - F^aux| <= n N' at t - h, t, t + h
        Saux = 1 + rng.rational(0, 2, 64)
        Np = N * rng.rational(0, 1, 64)
        e = [n * Np * rng.rational(-1, 1, 64) for _ in range(3)]
        S = Saux + (e[0] + e[2] - 2 * e[1]) / hh
        F.ok(GE(S, Saux - 4 * n * Np / hh) and GE(S, Q(5, 8)) and GT(S, HALF), "chain S_h(t) >= 5/8 > 1/2")
    F.note("2000 sampled chains with n = 2..200 and 0 < h <= 1")

    def worst(n, hh, coef):
        gamma, sgv, N, low = prop31_lower(n, hh, 96, 2 ** 20, 4)
        e = [-n * N, n * N, -n * N]
        S = 1 + (e[0] + e[2] - 2 * e[1]) / hh
        return GE(S, 1 - coef * n * N / hh), S

    ok_w, S_w = worst(5, Q(1, 3), 4)
    F.ok(ok_w and EQ(S_w, Q(5, 8)), "worst case attains 5/8")
    F.control("N1", "2^18 instead of 2^20 in gamma: 1 - 384/512 > 1/2",
              GT(prop31_lower(5, Q(1, 3), 96, 2 ** 18, 4)[3], HALF))
    F.control("N2", "nuclear constant 192 instead of 96: 1 - 768/1024 > 1/2",
              GT(prop31_lower(5, Q(1, 3), 192, 2 ** 20, 4)[3], HALF))
    F.control("N3", "transfer coefficient 3 instead of 4 (worst-case errors)", worst(5, Q(1, 3), 3)[0])
    # (28) on exact diagonal pairs: |F(A + sX) - F(B + sX)| <= n ||A - B||_* (nuclear norm = sum |a_i - b_i|).
    for _ in range(600):
        n = rng.integer(1, 8)
        A = [rng.rational(-1, 1, 32) for _ in range(n)]
        B = [rng.rational(-1, 1, 32) for _ in range(n)]
        s = rng.rational(-1, 1, 32)
        nuc = sum((abs(A[i] - B[i]) for i in range(n)), Q(0))
        F.ok(LE(abs(F_diag(A, s) - F_diag(B, s)), n * nuc), "(28) on diagonal pairs")
    A = [Q(0), Q(1, 4), Q(1, 2), Q(3, 4)]
    B = A[:3] + [Q(4, 5)]
    F.control("N4", "(28) with weight n - 1 instead of n",
              LE(abs(F_diag(A, 0) - F_diag(B, 0)), 3 * sum((abs(A[i] - B[i]) for i in range(4)), Q(0))))


# ================================================================ C09

def fam_c09(F):
    """Lemma 4.1, (29) and (30): triangular weights, the constant 4/3, the factor 2/3 and the tolerance h/256."""
    rng = Rng("C09")
    wP = lambda u: tri_w(Q(0), Q(1), u)
    wL = lambda u: tri_w(Q(-1, 4), Q(1, 4), u)
    wR = lambda u: tri_w(Q(1, 4), Q(1, 4), u)
    bps = [Q(-2), Q(-1), Q(-1, 2), Q(-1, 4), Q(0), Q(1, 4), Q(1, 2), Q(1), Q(2)]
    for u in bps:
        F.ok(GE(Q(4, 3) * wP(u) - wL(u) - wR(u), 0), "weight inequality at a breakpoint")
    F.note("weight inequality: the difference (4/3)w - w_L - w_R is piecewise linear with breakpoints "
           "-1,-1/2,-1/4,0,1/4,1/2,1 and vanishes outside [-1,1]; nonnegativity at the breakpoints "
           "is therefore a complete finite verification in the normalized variable (x - t)/h")
    ratios = [(wL(u) + wR(u)) / wP(u) for u in bps if wP(u) > 0]
    F.ok(EQ(max(ratios), Q(4, 3)) and [u for u in bps if wP(u) > 0 and EQ((wL(u) + wR(u)) / wP(u), Q(4, 3))]
         == [Q(-1, 4), Q(1, 4)], "extremal value 4/3, attained exactly at x = t -+ h/4")
    F.control("N1", "weight constant 5/4 instead of 4/3", ALL(GE(Q(5, 4) * wP(u) - wL(u) - wR(u), 0) for u in bps))
    for _ in range(3000):
        t = rng.rational(-2, 2, 64)
        hh = rng.rational(Q(1, 64), 2, 64)
        x = t + hh * rng.rational(-Q(3, 2), Q(3, 2), 96)
        F.ok(LE(tri_w(t - hh / 4, hh / 4, x) + tri_w(t + hh / 4, hh / 4, x), Q(4, 3) * tri_w(t, hh, x)),
             "weight inequality at a sample point")
    F.ok(EQ(HALF * Q(4, 3), Q(2, 3)), "(1/2)(4/3) = 2/3")
    # Measure representation and (29) on random convex piecewise-linear F (F'' = sum 2 a_i delta_{c_i}).
    insts = []
    for _ in range(1500):
        t = rng.rational(-1, 1, 64)
        hh = rng.rational(Q(1, 64), 1, 64)
        pool = [t + hh * Q(k, 8) for k in range(-9, 10)]
        kinks = []
        for _k in range(rng.integer(1, 6)):
            c = pool[rng.below(len(pool))] if rng.below(2) else t + hh * rng.rational(-Q(3, 2), Q(3, 2), 128)
            kinks.append((c, rng.rational(0, 2, 16)))
        Fp = PL(rng.rational(-3, 3, 8), rng.rational(-1, 1, 8), kinks)
        insts.append((Fp, t, hh))
        F.ok(EQ(S_c(Fp, t, hh), sum((2 * a * tri_w(t, hh, c) for c, a in Fp.kinks), Q(0))),
             "S_h(t) = integral of w_{t,h} against F''")
        F.ok(LE(min(S_c(Fp, t - hh / 4, hh / 4), S_c(Fp, t + hh / 4, hh / 4)), Q(2, 3) * S_c(Fp, t, hh)), "(29)")
    t, hh = Q(0), Q(1)
    sharp = PL(0, 0, [(-hh / 4, Q(1)), (hh / 4, Q(1))])
    F.ok(EQ(min(S_c(sharp, -hh / 4, hh / 4), S_c(sharp, hh / 4, hh / 4)), Q(2, 3) * S_c(sharp, t, hh)),
         "(29) is sharp: equality for kinks at t -+ h/4")
    F.control("N2", "(29) with factor 1/2 instead of 2/3 (sharp instance)",
              LE(min(S_c(sharp, -hh / 4, hh / 4), S_c(sharp, hh / 4, hh / 4)), HALF * S_c(sharp, t, hh)))
    r = sym("r")
    F.ok(((1 + 2 + 1) * (r / 256) / r).same(Q(1, 64)) and EQ(2 * Q(1, 64), Q(1, 32)),
         "(1+2+1)(r/256)/r = 1/64 and 2/64 = 1/32")

    # (30) for one refinement of Algorithm 1 with arbitrary replies within (h/4)/256 (ties go left).
    def refine1(Fp, t, hh, tol_den, rng, extreme):
        r = hh / 4
        tol = r / tol_den
        pts = [t - 2 * r, t - r, t, t + r, t + 2 * r]
        rep = []
        for x in pts:
            e = (tol if rng.below(2) else -tol) if extreme else tol * rng.rational(-1, 1, 8)
            rep.append(Fp(x) + e)
        SL = (rep[2] - 2 * rep[1] + rep[0]) / r
        SR = (rep[4] - 2 * rep[3] + rep[2]) / r
        errs = [abs(SL - S_c(Fp, t - r, r)), abs(SR - S_c(Fp, t + r, r))]
        nt = t - r if SL <= SR else t + r
        return nt, r, errs

    lo_s, hi_s = Q(3), Q(6)                      # (9) for n = 2
    worst_err = Q(0)
    for i in range(1500):
        t = rng.rational(Q(1, 8), Q(7, 8), 256)
        hh = rng.rational(Q(1, 256), Q(1, 8), 256)
        Fp = random_pl(rng, lo_s, hi_s, t, hh * 2, rng.integer(1, 6))
        nt, r, errs = refine1(Fp, t, hh, 256, rng, i % 2 == 0)
        worst_err = max(worst_err, max(errs))
        F.ok(ALL(LE(e, Q(1, 64)) for e in errs), "estimate error <= 1/64")
        F.ok(LE(S_c(Fp, nt, r), Q(2, 3) * S_c(Fp, t, hh) + Q(1, 32)), "(30) one refinement")
    F.ok(EQ(worst_err, Q(1, 64)), "the error bound 1/64 is attained by extreme replies")
    bad = []
    rng2 = Rng("C09-control")
    for _ in range(50):
        Fp = random_pl(rng2, lo_s, hi_s, HALF, Q(1, 4), 3)
        bad.append(max(refine1(Fp, HALF, Q(1, 8), 128, rng2, True)[2]))
    F.control("N3", "tolerance r/128 instead of r/256: estimate error <= 1/64", ALL(LE(e, Q(1, 64)) for e in bad))


# ================================================================ C10

def basic_Kb(n):
    m = 16 * n ** 3
    K, p3, p2 = 0, 1, 1
    while p3 < m * p2:
        K, p3, p2 = K + 1, p3 * 3, p2 * 2
    return K


def basic_Kb_bisect(n):
    m = 16 * n ** 3
    lo, hi = 0, 1
    while 3 ** hi < m * 2 ** hi:
        hi *= 2
    while lo < hi:
        mid = (lo + hi) // 2
        if 3 ** mid >= m * 2 ** mid:
            hi = mid
        else:
            lo = mid + 1
    return lo


def fam_c10(F):
    """Theorem 4.1, Remark 4.1, (31), (32): K_b, (2/3)^{K_b} n^3 <= 1/16, 5/32 + 2/64 < 1/2, 3 + 5 K_b."""
    kb_max = 0
    for n in range(2, N_MAX + 1):
        Kb = basic_Kb(n)
        kb_max = max(kb_max, Kb)
        m = 16 * n ** 3
        F.ok(Kb == basic_Kb_bisect(n) and GE(3 ** Kb, m * 2 ** Kb) and LT(3 ** (Kb - 1), m * 2 ** (Kb - 1)),
             "K_b least with (3/2)^K_b >= 16 n^3 (two methods)")
        F.ok(LE(Q(2 ** Kb, 3 ** Kb) * n ** 3, Q(1, 16)), "(2/3)^K_b n^3 <= 1/16")
        sKb = Q(2 ** Kb, 3 ** Kb) * n ** 3 + Q(1, 32) * 3 * (1 - Q(2 ** Kb, 3 ** Kb))
        F.ok(LT(sKb, Q(5, 32)), "s_K_b < 5/32 (worst case s_0 = n^3)")
        # (32): 4^{-K_b} > (1/4)(16n^3)^{-alpha}  <=>  (3/2)^{K_b - 1} < 16 n^3 (alpha = log_{3/2} 4).
        F.ok(LT(3 ** (Kb - 1), m * 2 ** (Kb - 1)), "(32) reduced: (3/2)^(K_b - 1) < 16 n^3")
    F.note("K_b, (2/3)^K_b n^3 <= 1/16, s_K_b < 5/32, (32): n = 2..%d (finite cross-check; max K_b = %d)"
           % (N_MAX, kb_max))
    F.note("(32) reduction: 4^(K_b-1) < (16n^3)^alpha <=> (K_b-1) < log_{3/2}(16n^3) <=> (3/2)^(K_b-1) < 16n^3, "
           "by monotonicity of log; only the last (integer) form is computed")
    for j in range(0, kb_max + 1):
        geo = sum((Q(2 ** l, 3 ** l) for l in range(j)), Q(0))
        F.ok(EQ(geo, 3 * (1 - Q(2 ** j, 3 ** j))) and LT(Q(1, 32) * geo, Q(3, 32)), "(1/32) sum (2/3)^l < 3/32")
    # Iterating (30): s_{j+1} = (2/3) s_j + 1/32 from s_0 = n^3 equals the closed form of the proof.
    for n in range(2, 101):
        Kb = basic_Kb(n)
        s = Q(n ** 3)
        for j in range(Kb + 1):
            closed = Q(2 ** j, 3 ** j) * n ** 3 + Q(1, 32) * sum((Q(2 ** l, 3 ** l) for l in range(j)), Q(0))
            F.ok(EQ(s, closed) and LT(closed, Q(2 ** j, 3 ** j) * n ** 3 + Q(3, 32)), "iteration closed form")
            s = Q(2, 3) * s + Q(1, 32)
    F.ok(EQ(Q(5, 32) + Q(2, 64), Q(3, 16)) and LT(Q(3, 16), HALF), "5/32 + 2/64 = 3/16 < 1/2")
    F.ok(EQ(Q(1, 16) + Q(3, 32), Q(5, 32)), "1/16 + 3/32 = 5/32")
    F.control("N1", "K_b - 1 refinements: (2/3)^(K_b - 1) n^3 <= 1/16 for all n",
              ALL(LE(Q(2 ** (basic_Kb(n) - 1), 3 ** (basic_Kb(n) - 1)) * n ** 3, Q(1, 16)) for n in range(2, 200)))
    F.control("N2", "K = ceil(log2(16 n^3)) refinements in place of K_b: (2/3)^K n^3 <= 1/16",
              ALL(LE(Q(2 ** (16 * n ** 3 - 1).bit_length(), 3 ** (16 * n ** 3 - 1).bit_length()) * n ** 3, Q(1, 16))
                  for n in range(2, 200)))
    # Radii: h_j = (delta/(2n)) 4^{-j}; (31) for j <= K_b; h <= delta/(2n) < 1 for 0 < delta < 1/2, n >= 2.
    for delta in (Q(1, 3), Q(49, 100), Q(1, 1000)):
        for n in (2, 3, 7, 50, N_MAX):
            Kb = basic_Kb(n)
            h0 = delta / (2 * n)
            F.ok(ALL(GE(h0 / 4 ** j, h0 / 4 ** Kb) for j in range(Kb + 1)) and LT(h0, 1), "(31) radius bound")
    # Evaluations: 3 initially, 5 distinct points t-2h, ..., t+2h per refinement; the test needs no new point.
    for r in (Q(1), Q(1, 7)):
        pts = [-2 * r, -r, Q(0), r, 2 * r]
        F.ok(len(set(pts)) == 5 and ALL(c + s * r in pts for c in (-r, r) for s in (-1, 0, 1)),
             "5 evaluations per refinement suffice and are needed")
    F.control("N3", "4 evaluations per refinement", LE(len(set([-2, -1, 0, 1, 2])), 4))


# ================================================================ C11

def fam_c11(F):
    """Lemma 4.2, (33)-(36): S_h <= S_h^(theta), the factor 1/2, the tolerance 2 theta h/256."""
    rng = Rng("C11")
    insts = []
    for _ in range(2500):
        t = rng.rational(-1, 1, 64)
        hh = rng.rational(Q(1, 64), 1, 64)
        th = [HALF, Q(1, 4), Q(1, 8), Q(1, 28), Q(1, 176), rng.rational(Q(1, 64), HALF, 64)][rng.below(6)]
        a = (1 - 2 * th) * hh
        pool = [t + s * x for s in (-1, 1) for x in (hh, a, a / 2, (1 - 2 * th) * a, 2 * th * a, Q(0))]
        kinks = []
        for _k in range(rng.integer(1, 6)):
            c = pool[rng.below(len(pool))] if rng.below(2) else t + hh * rng.rational(-Q(3, 2), Q(3, 2), 128)
            kinks.append((c, rng.rational(0, 2, 16)))
        Fp = PL(rng.rational(-3, 3, 8), 0, kinks)
        insts.append((Fp, t, hh, th))
        F.ok(GE(S_c(Fp, t, hh), 0) and GE(S_e(Fp, th, t, hh), 0), "(13), (33) nonnegative")
        F.ok(LE(S_c(Fp, t, hh), S_e(Fp, th, t, hh)), "(34) for 0 < theta <= 1/2")
        if th <= Q(1, 4):
            hp = (HALF - th) * hh
            cl, cr = S_e(Fp, th, t - hp, hp), S_e(Fp, th, t + hp, hp)
            F.ok(LE(cl + cr, S_e(Fp, th, t, hh)), "child endpoint variations sum to at most the parent")
            F.ok(LE(min(cl, cr), HALF * S_e(Fp, th, t, hh)), "(35)")
            sig = lambda x, y: (Fp(y) - Fp(x)) / (y - x)
            F.ok(LE(sig(t - hh, t - 2 * hp), sig(t - 2 * hp, t - 2 * hp + 2 * th * hp))
                 and LE(sig(t - 2 * th * hp, t), sig(t, t + 2 * th * hp))
                 and LE(sig(t + 2 * hp - 2 * th * hp, t + 2 * hp), sig(t + 2 * hp, t + hh)),
                 "the three secant orderings of the proof of Lemma 4.2")
    absF = PL(0, 0, [(Q(0), Q(1))])
    F.control("N1", "(34) for theta = 1", LE(S_c(absF, Q(0), Q(1)), S_e(absF, Q(1), Q(0), Q(1))))
    th, hh = Q(1, 8), Q(1)
    hp = (HALF - th) * hh
    sharp = PL(0, 0, [(-hp, Q(1)), (hp, Q(1))])
    cl, cr = S_e(sharp, th, -hp, hp), S_e(sharp, th, hp, hp)
    F.ok(EQ(min(cl, cr), HALF * S_e(sharp, th, Q(0), hh)), "(35) is sharp: kinks at the candidate centres")
    F.control("N2", "(35) with factor 1/3 instead of 1/2 (sharp instance)", LE(min(cl, cr), Q(1, 3) * S_e(sharp, th, 0, hh)))
    thv, hv = sym("theta"), sym("h")
    F.ok((4 * (2 * thv * hv / 256) / (2 * thv * hv)).same(Q(1, 64)), "4 (2 theta h/256)/(2 theta h) = 1/64")

    # (36) for one refinement with arbitrary replies within 2 theta h'/256 (ties go left), n = 2 slopes.
    def refine2(Fp, t, hh, th, tol_mult, rng, extreme):
        hp = (HALF - th) * hh
        tol = tol_mult * 2 * th * hp / 256
        pts = [t - 2 * hp, t - 2 * hp + 2 * th * hp, t - 2 * th * hp, t, t + 2 * th * hp, t + 2 * hp - 2 * th * hp,
               t + 2 * hp]
        v = [Fp(x) + ((tol if rng.below(2) else -tol) if extreme else tol * rng.rational(-1, 1, 8)) for x in pts]
        SL = (v[3] - v[2] - v[1] + v[0]) / (2 * th * hp)
        SR = (v[6] - v[5] - v[4] + v[3]) / (2 * th * hp)
        errs = [abs(SL - S_e(Fp, th, t - hp, hp)), abs(SR - S_e(Fp, th, t + hp, hp))]
        nt = t - hp if SL <= SR else t + hp
        return nt, hp, errs, pts

    worst_err = Q(0)
    for i in range(1500):
        t = rng.rational(Q(1, 8), Q(7, 8), 256)
        hh = rng.rational(Q(1, 256), Q(1, 8), 256)
        th = [Q(1, 4), Q(1, 28), Q(1, 48), rng.rational(Q(1, 64), Q(1, 4), 64)][rng.below(4)]
        Fp = random_pl(rng, Q(3), Q(6), t, hh * 2, rng.integer(1, 6))
        nt, hp, errs, pts = refine2(Fp, t, hh, th, 1, rng, i % 2 == 0)
        worst_err = max(worst_err, max(errs))
        F.ok(ALL(LE(e, Q(1, 64)) for e in errs), "estimate error <= 1/64")
        F.ok(LE(S_e(Fp, th, nt, hp), HALF * S_e(Fp, th, t, hh) + Q(1, 32)), "(36) one refinement")
        F.ok(len(set(pts + [nt])) == 8 and ALL(LE(t - hh, x) and LE(x, t + hh) for x in pts),
             "7 distinct requested points in the parent window; new centre distinct")
    F.ok(EQ(worst_err, Q(1, 64)), "the error bound 1/64 is attained by extreme replies")
    bad = []
    rng2 = Rng("C11-control")
    for _ in range(50):
        Fp = random_pl(rng2, Q(3), Q(6), HALF, Q(1, 4), 3)
        bad.append(max(refine2(Fp, HALF, Q(1, 8), Q(1, 28), 2, rng2, True)[2]))
    F.control("N3", "tolerance doubled to 4 theta h'/256: estimate error <= 1/64", ALL(LE(e, Q(1, 64)) for e in bad))


# ================================================================ C12

def doubling_K(n):
    """Algorithm 2, line 1: K by doubling and comparisons."""
    target = 16 * n ** 3
    K, P = 0, 1
    while P < target:
        K, P = K + 1, 2 * P
    return K


def fam_c12(F):
    """Algorithm 2, Theorem 4.2, (37)-(40), Theorem 1.1 and (5): K, theta, Bernoulli, h > delta/(128 n^4), 2^-34."""
    bern = {}
    for K in range(1, K_MAX + 1):
        ok = GE(2 * (2 * K - 1) ** K, (2 * K) ** K)
        bern[K] = ok
        F.ok(ok, "(1 - 1/(2K))^K >= 1/2")
    F.note("Bernoulli (1 - 1/(2K))^K >= 1/2: K = 1..%d (finite cross-check)" % K_MAX)
    geo = {}
    npts = {}
    kmax = 0
    for n in range(2, N_MAX + 1):
        K = doubling_K(n)
        kmax = max(kmax, K)
        m = 16 * n ** 3
        th = Q(1, 4 * K)
        F.ok(K == (m - 1).bit_length() and GE(2 ** K, m) and LT(2 ** (K - 1), m),
             "K by doubling = least K with 2^K >= 16 n^3 = ceil(log2(16 n^3))")
        F.ok(LT(2 ** K, 32 * n ** 3), "2^K < 32 n^3")
        F.ok(K >= 7 and LE(th, Q(1, 28)) and LE(th, Q(1, 4)), "theta = 1/(4K) <= 1/28 <= 1/4")
        if K not in geo:
            geo[K] = Q(1, 32) * sum((Q(1, 2 ** j) for j in range(K)), Q(0))
        F.ok(LE(Q(n ** 3, 2 ** K), Q(1, 16)) and LT(geo[K], Q(1, 16)) and LT(Q(n ** 3, 2 ** K) + geo[K], Q(1, 8)),
             "2^-K n^3 + (1/32) sum 2^-j < 1/16 + 1/16 = 1/8")
        F.ok(EQ(4 * (2 * th * 1) / 256 / 1, th / 32) and LE(th / 32, Q(1, 128))
             and LT(Q(1, 8) + Q(1, 128) + Q(1, 64), HALF), "theta/32 <= 1/128 and 1/8 + 1/128 + 1/64 < 1/2")
        # L_K = (delta/n)(1/2 - theta)^K = (delta/n) 2^-K (1 - 1/(2K))^K > delta/(64 n^4)
        lk = Q((2 * K - 1) ** K, (4 * K) ** K)
        F.ok(EQ(lk, Q(1, 2 ** K) * Q((2 * K - 1) ** K, (2 * K) ** K)) and bern[K]
             and GT(Q(1, 2 ** K), Q(1, 32 * n ** 3)) and GT(lk, Q(1, 64 * n ** 3)),
             "(1/2 - theta)^K > 1/(64 n^3), i.e. L_K > delta/(64 n^4)")
        # h_K = L_K/2 > delta/(128 n^4); (40): smallest tolerance 2 theta h_K/256 = h_K/(512 K) > delta/(2^16 K n^4)
        hK = lk / (2 * n)
        F.ok(GT(hK, Q(1, 128 * n ** 4)) and EQ(2 * th * hK / 256, hK / (512 * K))
             and GT(hK / (512 * K), Q(1, 2 ** 16 * K * n ** 4)) and GE(Q(1, 2 * n) / 256, hK / (512 * K)),
             "(37) h > delta/(128 n^4) and (40) eps_min > delta/(2^16 K n^4)  [delta factored out]")
        if K not in npts:
            pts = [Q(-2), -2 + 2 * th, -2 * th, Q(0), 2 * th, 2 - 2 * th, Q(2)]
            npts[K] = (len(set(pts)), len(set(pts + [Q(-1)])), len(set(pts + [Q(1)])),
                       ALL(c + s in pts for c in (-1, 1) for s in (-1, 1)))
        F.ok(npts[K][0] == 7 and npts[K][1] == 8 and npts[K][2] == 8 and npts[K][3]
             and K <= 4 + 3 * (n - 1).bit_length(),
             "8 distinct evaluations per refinement (so at most 3 + 8K); K <= 4 + 3 ceil(log2 n)")
    F.note("K, theta, (1/2-theta)^K > 1/(64n^3), (37), (40): n = 2..%d (finite cross-check; K <= %d)" % (N_MAX, kmax))
    F.control("N1", "K - 1 refinements: 2^(K-1) >= 16 n^3", ALL(GE(2 ** (doubling_K(n) - 1), 16 * n ** 3)
                                                                for n in range(2, 300)))
    F.control("N2", "theta = 1/(2K): (1/2 - theta)^K > 1/(64 n^3) for all n <= %d" % N_MAX,
              ALL(GT(Q((doubling_K(n) - 1) ** doubling_K(n), (2 * doubling_K(n)) ** doubling_K(n)), Q(1, 64 * n ** 3))
                  for n in range(2, N_MAX + 1)))
    F.control("N3", "Bernoulli bound 3/4 instead of 1/2 at K = 1", GE(4 * (2 * 1 - 1) ** 1, 3 * (2 * 1) ** 1))
    # Symbolic reduction: h > c delta n^-4  =>  h^2/(2^20 n^4) > c^2 2^-20 delta^2 n^-12; c = 1/128 gives 2^-34.
    d, nn, hv, Kv = sym("delta"), sym("n"), sym("h"), sym("K")

    def reduce_gap(c):
        hmin = Mono(c) * d / nn ** 4
        return (hmin ** 2 / (Mono(2 ** 20) * nn ** 4)).same(Mono(Q(1, 2 ** 34)) * d ** 2 / nn ** 12)

    F.ok(reduce_gap(Q(1, 128)), "symbolic: (delta/(128 n^4))^2/(2^20 n^4) = 2^-34 delta^2 n^-12")
    F.ok(EQ(128 ** 2 * 2 ** 20, 2 ** 34), "128^2 * 2^20 = 2^34")
    F.ok((d / nn * (Mono(Q(1, 32)) / nn ** 3) * HALF).same(d / (64 * nn ** 4)),
         "symbolic: (delta/n)(1/(32 n^3))(1/2) = delta/(64 n^4)")
    F.ok((hv / (512 * Kv)).same(2 * (Mono(1) / (4 * Kv)) * hv / 256)
         and ((d / (128 * nn ** 4)) / (512 * Kv)).same(d / (Mono(2 ** 16) * Kv * nn ** 4)),
         "symbolic: 2 theta h/256 = h/(512 K) and (delta/(128 n^4))/(512 K) = delta/(2^16 K n^4)")
    samples = []
    for delta in (Q(1, 3), Q(49, 100), Q(1, 7), Q(1, 10 ** 6)):
        for n in (2, 3, 5, 10, 97, 1000, N_MAX):
            hmin = delta / (128 * n ** 4)
            for hh in (hmin * Q(1001, 1000), hmin * 2, delta / (2 * n)):
                F.ok(GT(hh * hh / (2 ** 20 * n ** 4), Q(1, 2 ** 34) * delta ** 2 / n ** 12), "sampled 2^-34 bound")
            F.ok(EQ(hmin * hmin / (2 ** 20 * n ** 4), Q(1, 2 ** 34) * delta ** 2 / n ** 12), "equality at h_min")
            F.ok(GE(Q(1, 2 ** 34) * delta ** 2 / n ** 12, Q(1, 2 ** 34) * (delta / n) ** 12),
                 "(5): 2^-34 delta^2 n^-12 >= 2^-34 (delta/n)^12")
            F.ok(LT(delta / (2 * n), 1) and LE(n * (delta / n), delta), "h <= delta/(2n) < 1 and ||tX|| = nt <= delta")
            samples.append((delta, n))
    # A constant larger than the proved one is false just above the minimal radius h > delta/(128 n^4).
    F.control("N4", "constant doubled: h > delta/(128 n^4) gives h^2/(2^20 n^4) > 2 * 2^-34 delta^2 n^-12",
              ALL(GT((delta / (128 * n ** 4) * Q(1001, 1000)) ** 2 / (2 ** 20 * n ** 4),
                     2 * Q(1, 2 ** 34) * delta ** 2 / n ** 12) for delta, n in samples))
    F.control("N5", "7 evaluations per refinement (7 endpoint points plus the new centre are distinct)",
              LE(len(set([Q(-2), Q(-2) + Q(2, 28), -Q(2, 28), Q(0), Q(2, 28), 2 - Q(2, 28), Q(2), Q(-1)])), 7))


# ================================================================ C13

def alg2_run(Fx, n, delta, oracle, margin=Q(1, 64)):
    """Algorithm 2 as a transcript (requests numbered from 0; ties go left)."""
    K = doubling_K(n)
    th = Q(1, 4 * K)
    log = []

    def req(x, tol):
        y = oracle(len(log), x, tol)
        log.append((x, tol, y))
        return y

    t = h = Q(delta) / (2 * n)
    hist = [(t, h)]
    tests = []
    fm, f0, fp = req(t - h, h / 256), req(t, h / 256), req(t + h, h / 256)
    est = (fp - 2 * f0 + fm) / h
    tests.append((t, h, est, Q(1, 64)))
    if est + margin < HALF:
        return dict(t=t, h=h, j=0, returned=True, log=log, hist=hist, tests=tests, K=K, th=th)
    for j in range(K):
        h = (HALF - th) * h
        tol = 2 * th * h / 256
        pts = [t - 2 * h, t - 2 * h + 2 * th * h, t - 2 * th * h, t, t + 2 * th * h, t + 2 * h - 2 * th * h, t + 2 * h]
        v = [req(x, tol) for x in pts]
        SL = (v[3] - v[2] - v[1] + v[0]) / (2 * th * h)
        SR = (v[6] - v[5] - v[4] + v[3]) / (2 * th * h)
        if SL <= SR:
            t, fm, fp = t - h, v[0], v[3]
        else:
            t, fm, fp = t + h, v[3], v[6]
        f0 = req(t, tol)
        est = (fp - 2 * f0 + fm) / h
        hist.append((t, h))
        tests.append((t, h, est, th / 32))
        if est + margin < HALF:
            return dict(t=t, h=h, j=j + 1, returned=True, log=log, hist=hist, tests=tests, K=K, th=th)
    return dict(t=t, h=h, j=K, returned=False, log=log, hist=hist, tests=tests, K=K, th=th)


def alg2_outcome(run, Fx, n, delta, diag=None):
    K, th, t, h = run["K"], run["th"], run["t"], run["h"]
    res = []
    res.append(("returned within K refinements", run["returned"] and run["j"] <= K))
    res.append(("3 + 8j requests <= 3 + 8K", len(run["log"]) == 3 + 8 * run["j"] and 3 + 8 * run["j"] <= 3 + 8 * K))
    res.append(("requests in [0, delta/n]", ALL(LE(0, x) and LE(x, delta / n) for x, _, _ in run["log"])))
    res.append(("(40) tolerances in (delta/(2^16 K n^4), 1)",
                ALL(GT(tol, Q(delta) / (2 ** 16 * K * n ** 4)) and LT(tol, 1) for _, tol, _ in run["log"])))
    hist = run["hist"]
    res.append(("h_j = (1/2 - theta)^j delta/(2n)", ALL(EQ(hist[j][1], (HALF - th) ** j * Q(delta) / (2 * n))
                                                       for j in range(len(hist)))))
    res.append(("windows nested in [0, delta/n]", ALL(LE(hist[j][0] - hist[j][1], hist[j + 1][0] - hist[j + 1][1])
                                                      and LE(hist[j + 1][0] + hist[j + 1][1], hist[j][0] + hist[j][1])
                                                      for j in range(len(hist) - 1))
                and LE(0, hist[0][0] - hist[0][1]) and LE(hist[0][0] + hist[0][1], Q(delta) / n)))
    se = [S_e(Fx, th, a, b) for a, b in hist]
    res.append(("initial endpoint variation < n^3", LT(se[0], n ** 3)))
    res.append(("(36) along the run", ALL(LE(se[j + 1], HALF * se[j] + Q(1, 32)) for j in range(len(se) - 1))))
    res.append(("stopping-test errors <= 1/64 (theta/32 after refinements)",
                ALL(LE(abs(est - S_c(Fx, a, b)), bound) and LE(bound, Q(1, 64)) for a, b, est, bound in run["tests"])))
    res.append(("(37) S_h(t) < 1/2", LT(S_c(Fx, t, h), HALF)))
    res.append(("(37) window in [0, delta/n] and h > delta/(128 n^4)",
                LE(0, t - h) and LE(t + h, Q(delta) / n) and GT(h, Q(delta) / (128 * n ** 4)) and LE(h, Q(delta) / (2 * n))
                and LT(Q(delta) / (2 * n), 1)))
    res.append(("h^2/(2^20 n^4) > 2^-34 delta^2 n^-12", GT(h * h / (2 ** 20 * n ** 4), Q(1, 2 ** 34) * Q(delta) ** 2 / n ** 12)))
    if diag is not None:
        lam = sorted(diag[i] + t * (i + 1) for i in range(n))
        gap = min(lam[i + 1] - lam[i] for i in range(n - 1))
        res.append(("(38) exact gap(T + tX) > h^2/(2^20 n^4) (diagonal T)", GT(gap, h * h / (2 ** 20 * n ** 4))))
    return res


def alg1_run(Fx, n, delta, oracle):
    Kb = basic_Kb(n)
    log = []

    def req(x, tol):
        y = oracle(len(log), x, tol)
        log.append((x, tol, y))
        return y

    t = h = Q(delta) / (2 * n)
    hist, tests = [(t, h)], []
    fm, f0, fp = req(t - h, h / 256), req(t, h / 256), req(t + h, h / 256)
    est = (fp - 2 * f0 + fm) / h
    tests.append((t, h, est))
    if est + Q(1, 64) < HALF:
        return dict(t=t, h=h, j=0, returned=True, log=log, hist=hist, tests=tests, Kb=Kb)
    for j in range(Kb):
        h = h / 4
        v = [req(x, h / 256) for x in (t - 2 * h, t - h, t, t + h, t + 2 * h)]
        SL = (v[2] - 2 * v[1] + v[0]) / h
        SR = (v[4] - 2 * v[3] + v[2]) / h
        if SL <= SR:
            t, est = t - h, SL
        else:
            t, est = t + h, SR
        hist.append((t, h))
        tests.append((t, h, est))
        if est + Q(1, 64) < HALF:
            return dict(t=t, h=h, j=j + 1, returned=True, log=log, hist=hist, tests=tests, Kb=Kb)
    return dict(t=t, h=h, j=Kb, returned=False, log=log, hist=hist, tests=tests, Kb=Kb)


def alg1_outcome(run, Fx, n, delta, diag=None):
    Kb, t, h = run["Kb"], run["t"], run["h"]
    res = []
    res.append(("returned within K_b refinements", run["returned"] and run["j"] <= Kb))
    res.append(("3 + 5j requests <= 3 + 5 K_b", len(run["log"]) == 3 + 5 * run["j"] and run["j"] <= Kb))
    res.append(("requests in [0, delta/n]", ALL(LE(0, x) and LE(x, Q(delta) / n) for x, _, _ in run["log"])))
    hist = run["hist"]
    sc = [S_c(Fx, a, b) for a, b in hist]
    res.append(("S_h0(t0) < n^3", LT(sc[0], n ** 3)))
    res.append(("(30) along the run", ALL(LE(sc[j + 1], Q(2, 3) * sc[j] + Q(1, 32)) for j in range(len(sc) - 1))))
    res.append(("test errors <= 1/64", ALL(LE(abs(est - S_c(Fx, a, b)), Q(1, 64)) for a, b, est in run["tests"])))
    res.append(("(31)", LE(0, t - h) and LE(t + h, Q(delta) / n) and LT(S_c(Fx, t, h), HALF)
                and GE(h, Q(delta) / (2 * n) / 4 ** Kb) and LT(h, 1)))
    if diag is not None:
        lam = sorted(diag[i] + t * (i + 1) for i in range(n))
        gap = min(lam[i + 1] - lam[i] for i in range(n - 1))
        res.append(("exact gap(T + tX) > h^2/(2^20 n^4) (diagonal T)", GT(gap, h * h / (2 ** 20 * n ** 4))))
    return res


def tree_pl(n, delta, ratio_of, levels):
    """Adversarial convex PL F: a kink of slope jump 13/25 at the centre of every window of the first
    `levels` levels of the refinement tree (child centre c -+ rho h, child radius rho h, rho = ratio_of(K)).
    The slopes stay in [n(n+1)/2, n^2(n+1)/2], so (9) holds; every such window has S_h(centre) >= 13/25."""
    lo, hi = fdiv(n * (n + 1), 2), fdiv(n * n * (n + 1), 2)
    jump = Q(13, 25)
    if jump * (2 ** levels - 1) > hi - lo:
        raise ValueError("slope budget exceeded")
    rho = ratio_of(doubling_K(n))
    t0 = Q(delta) / (2 * n)
    centres, level, h = [], [t0], t0
    for _ in range(levels):
        centres += level
        h = rho * h
        level = [c + s * h for c in level for s in (-1, 1)]
    return PL((lo + hi) / 2, 0, [(c, jump / 2) for c in centres])


def make_oracle(Fx, kind, rng):
    if kind == "exact":
        return lambda i, x, tol: Fx(x)
    if kind == "grid":
        return lambda i, x, tol: Fx(x) + tol * rng.rational(-1, 1, 8)
    return lambda i, x, tol: Fx(x) + (tol if rng.below(2) else -tol)


def fam_c13(F):
    """Algorithms 1 and 2 (Theorems 4.1 and 4.2) as transcripts on exact instances with bounded-error replies."""
    rng = Rng("C13")
    runs = 0
    maxj2 = 0
    for n in (2, 3, 4, 5, 6):
        lo_s, hi_s = fdiv(n * (n + 1), 2), fdiv(n * n * (n + 1), 2)
        for delta in (Q(1, 3), Q(49, 100), Q(1, 1000)):
            t0 = delta / (2 * n)
            K = doubling_K(n)
            th = Q(1, 4 * K)
            h1 = (HALF - th) * t0
            insts = []
            insts.append(("diag", [-(i + 1) * t0 for i in range(n)]))
            insts.append(("diag", [-(i + 1) * (t0 - h1) + h1 * rng.rational(-1, 1, 64) / 64 for i in range(n)]))
            insts.append(("diag", [rng.rational(-1, 1, 1 << 10) for _ in range(n)]))
            insts.append(("pl", random_pl(rng, lo_s, hi_s, t0, t0 / 8, 6)))
            insts.append(("pl", random_pl(rng, lo_s, hi_s, t0 - h1, h1 / 64, 4)))
            for kind, obj in insts:
                if kind == "diag":
                    d = obj
                    if not ALL(LE(abs(x), 1) for x in d):
                        raise ValueError("||T|| > 1")
                    Fx = (lambda dd: (lambda x: F_diag(dd, x)))(d)
                else:
                    d = None
                    Fx = obj
                for ok_kind in ("exact", "grid", "extreme"):
                    r2 = alg2_run(Fx, n, delta, make_oracle(Fx, ok_kind, rng))
                    maxj2 = max(maxj2, r2["j"])
                    for what, v in alg2_outcome(r2, Fx, n, delta, d):
                        F.ok(v, "Algorithm 2: " + what)
                    r1 = alg1_run(Fx, n, delta, make_oracle(Fx, ok_kind, rng))
                    for what, v in alg1_outcome(r1, Fx, n, delta, d):
                        F.ok(v, "Algorithm 1: " + what)
                    runs += 1
    # Adversarial kink trees force deep refinement (each tree window fails the stopping test).
    maxj1 = 0
    truns = 0
    for n, lv2, lv1 in ((3, 4, 4), (4, 5, 5), (5, 6, 6), (6, 7, 7), (8, 8, 8)):
        for delta in (Q(1, 3), Q(49, 100)):
            for alg, lv in ((2, lv2), (1, lv1)):
                ratio = (lambda K: HALF - Q(1, 4 * K)) if alg == 2 else (lambda K: Q(1, 4))
                Fx = tree_pl(n, delta, ratio, lv)
                for ok_kind in ("exact", "grid", "extreme"):
                    if alg == 2:
                        r = alg2_run(Fx, n, delta, make_oracle(Fx, ok_kind, rng))
                        maxj2 = max(maxj2, r["j"])
                        res = alg2_outcome(r, Fx, n, delta)
                    else:
                        r = alg1_run(Fx, n, delta, make_oracle(Fx, ok_kind, rng))
                        maxj1 = max(maxj1, r["j"])
                        res = alg1_outcome(r, Fx, n, delta)
                    F.ok(r["j"] >= lv, "kink tree forces at least %d refinements" % lv)
                    for what, v in res:
                        F.ok(v, "Algorithm %d (kink tree): %s" % (alg, what))
                    truns += 1
    F.note("%d runs of each algorithm: n = 2..6, delta in {1/3, 49/100, 1/1000}, exact diagonal T and convex "
           "piecewise-linear F satisfying (9), exact/grid/extreme replies within the tolerances" % runs)
    F.note("%d runs on adversarial kink trees (n = 3, 4, 5, 6, 8; all levels the slope budget (9) allows): "
           "up to %d refinements of Algorithm 2 (K <= 13) and "
           "%d of Algorithm 1" % (truns, maxj2, maxj1))
    # Controls: replies violating the tolerance, and the stopping margin 1/64 removed.
    n, delta = 2, Q(1, 4)
    t0 = delta / (2 * n)
    peak = PL(Q(9, 2), 0, [(t0, Q(3, 2))])            # slopes 3 and 6: (9) for n = 2; S_h0(t0) = 3
    F.ok(EQ(S_c(peak, t0, t0), 3), "control instance: S_h0(t0) = 3")
    liar = lambda i, x, tol: peak(x) + (Q(3, 2) * t0 if x == t0 and i == 1 else 0)
    r = alg2_run(peak, n, delta, liar)
    F.control("N1", "replies outside the tolerance (Algorithm 2 then returns with S_h(t) = 3)",
              ALL(v for _, v in alg2_outcome(r, peak, n, delta)))
    half_peak = PL(Q(9, 2), 0, [(t0, Q(1, 4))])        # S_h0(t0) = 1/2
    push = lambda i, x, tol: half_peak(x) + (tol if x == t0 else 0)
    r = alg2_run(half_peak, n, delta, push, margin=Q(0))
    F.ok(EQ(S_c(half_peak, t0, t0), HALF) and r["j"] == 0, "control instance: returns at the initial test")
    F.control("N2", "stopping test without the margin 1/64 (returns a window with S_h(t) = 1/2)",
              ALL(v for _, v in alg2_outcome(r, half_peak, n, delta)))


# ================================================================ C14

def fam_c14(F):
    """Lemma 4.3, Section 4.3 and Appendix A parameters: eta = eps/sum j, R >= 8n/eta by doubling, 2^x - 1 <= x."""
    eps_list = [Q(1, 2), Q(1, 3), Q(99, 100), Q(1, 1000), Q(1, 10 ** 9)]
    for n in list(range(1, 129)) + [1000, N_MAX]:
        sj = sum(range(1, n + 1))
        for eps in eps_list:
            eta = eps / sj
            F.ok(EQ(eta, 2 * eps / (n * (n + 1))) and EQ(Q(n * (n + 1), 2) * eta, eps), "eta = eps/sum j = 2eps/(n(n+1))")
            F.ok(LE(n / eta, (n / eps) ** 3), "n/eta <= (n/eps)^3 for 0 < eps < 1")
            R, k = 1, 0
            while R * eta < 8 * n:
                R, k = 2 * R, k + 1
            F.ok(GE(R * eta, 8 * n) and (k == 0 or LT(R * eta / 2, 8 * n)) and LT(R * eta, 16 * n),
                 "R = 2^k least with R eta >= 8n, so 8n/eta <= R < 16n/eta")
            F.ok(n <= R and LE(Q(4 * n, R), eta / 2), "n <= R and 4n/R <= eta/2")
            F.ok(EQ(sum((j * (eta / 2) for j in range(1, n + 1)), Q(0)), eps / 2) and LE(eps / 2, eps),
                 "sum_j j eta/2 = eps/2 <= eps")
    F.note("parameters: n = 1..128, 1000, %d and eps in {1/2, 1/3, 99/100, 1/1000, 1e-9}" % N_MAX)

    # 2^x - 1 <= x and 1 - 2^-x <= x for x = p/q in [0, 1]:  2^p q^q <= (q+p)^q  and  (q-p)^q 2^p <= q^q.
    def pow2_le(p, q):
        return LE(2 ** p * q ** q, (q + p) ** q)

    def pow2m_le(p, q):
        return LE((q - p) ** q * 2 ** p, q ** q)

    for q in range(1, 41):
        for p in range(0, q + 1):
            F.ok(pow2_le(p, q) and pow2m_le(p, q), "2^x - 1 <= x and 1 - 2^-x <= x at x = p/q")
    for n in (1, 2, 5, 8):
        for k in range(0, 13):
            R = 2 ** k
            if R >= n:
                F.ok(pow2_le(n, R) and pow2m_le(n, R), "x = n/R <= 1")
    F.note("2^x - 1 <= x and 1 - 2^-x <= x: all x = p/q in [0,1] with q <= 40, and x = n/R (sampled)")
    # |r^ - r| <= r (2^{n/R} - 1) <= r n/R < 4n/R for 0 < r < 4 (sampled exactly with x = n/R).
    for n, R in ((1, 8), (3, 64), (8, 512), (8, 8)):
        x = Q(n, R)
        for r in (Q(1, 100), Q(1), Q(7, 2), Q(399, 100)):
            F.ok(LE(r * x, Q(4 * n, R)) and LT(r * x, Q(4 * n, R)), "r n/R < 4n/R for r < 4")
    F.control("N1", "2^x - 1 <= x at x = 3/2 (outside [0, 1]): 2^3 * 2^2 <= 5^2", LE(2 ** 3 * 2 ** 2, 5 ** 2))
    F.control("N2", "2^x - 1 <= x at x = -1/2: 2^(-1/2) <= 1/2", LE(Q(1, 2), Q(1, 4)))

    def target_ok(mult):
        good = True
        for n in range(1, 65):
            for eps in eps_list:
                eta = eps / sum(range(1, n + 1))
                R = 1
                while R * eta < mult * n:
                    R *= 2
                good = good and LE(Q(4 * n, R), eta / 2)
        return good

    F.ok(target_ok(8), "doubling target 8n")
    F.control("N3", "doubling target 4n instead of 8n: 4n/R <= eta/2", target_ok(4))
    def total_ok(eta_num):
        # eta = eta_num * eps/(n(n+1)); total error sum_j j eta/2 <= eps   (the paper: eta_num = 2)
        good = True
        for n in range(1, 129):
            for eps in eps_list:
                eta = eta_num * eps / (n * (n + 1))
                good = good and LE(sum((j * (eta / 2) for j in range(1, n + 1)), Q(0)), eps)
        return good

    F.ok(total_ok(2), "total error <= eps for eta = 2 eps/(n(n+1))")
    F.control("N4", "eta = 8 eps/(n(n+1)) (four times eps/sum j): total error <= eps", total_ok(8))


# ================================================================ driver

FAMILIES = [
    ("C01", "Lemma 2.1, (8)-(10), S_h(t) < n^3 [secant slopes, tail sums]", fam_c01),
    ("C02", "Examples 2.2, 2.3, 3.1, 3.2, 4.1 [exactly checkable claims]", fam_c02),
    ("C03", "Lemma 3.1 Step 1, (21) [1/4, 3/4, 3/8, sqrt(3/8) > 1/2]", fam_c03),
    ("C04", "Lemma 3.1 Step 2, (22) [discrete Wronskian identity, bound 1/2]", fam_c04),
    ("C05", "Lemma 3.1 Step 3, (23) [tau, cases (a)-(c), 5/16 < 1/2]", fam_c05),
    ("C06", "Lemma 3.1 Step 4, (20) [residuals, commutator, 16 n sqrt(gamma)]", fam_c06),
    ("C07", "Lemma 3.2, (26)-(27) [AQ + QA - QAQ, 96 n sqrt(gamma), S^aux >= 1]", fam_c07),
    ("C08", "Proposition 3.1, (19), (28) [2^20, transfer 4, 5/8 > 1/2]", fam_c08),
    ("C09", "Lemma 4.1, (29)-(30) [weights, 4/3, 2/3, h/256 -> 1/64]", fam_c09),
    ("C10", "Theorem 4.1, Remark 4.1, (31)-(32) [K_b, 5/32 + 2/64 < 1/2, 3 + 5K_b]", fam_c10),
    ("C11", "Lemma 4.2, (33)-(36) [S_h <= S_h^(theta), 1/2, 2 theta h/256 -> 1/64]", fam_c11),
    ("C12", "Algorithm 2, Theorem 4.2, (37)-(40), Theorem 1.1, (5) [K, theta, Bernoulli, 2^-34]", fam_c12),
    ("C13", "Algorithms 1 and 2 as transcripts, Theorems 4.1 and 4.2 [exact instances]", fam_c13),
    ("C14", "Lemma 4.3, Section 4.3, Appendix A [eta, R >= 8n/eta, 2^x - 1 <= x, total error]", fam_c14),
]


def main(argv):
    FAULT[0] = False
    if argv == ["--inject-fault"]:
        FAULT[0] = True
    elif argv:
        print("FAIL: usage: check_constants.py [--inject-fault]")
        return 2
    if sys.version_info < (3, 11):
        print("FAIL: Python 3.11 or later is required")
        return 1
    print("== %s: KE-02 exact checks of constants and inequality chains ==" % NAME)
    print("exact integer/rational arithmetic only; finite cross-checks (ranges stated per family)")
    total_checks, total_controls, failed = 0, 0, 0
    for fid, title, fn in FAMILIES:
        fam = Family(fid, title)
        try:
            fn(fam)
        except Exception as exc:          # fail closed
            fam.fails.append("exception %s: %s" % (type(exc).__name__, exc))
        if fam.checks == 0:
            fam.fails.append("no checks executed")
        if not fam.controls:
            fam.fails.append("no negative controls rejected")
        if fam.fails:
            failed += 1
            print("FAIL: %s %s: %d failure(s), %d checks passed" % (fid, title, len(fam.fails), fam.checks))
            for f in fam.fails[:5]:
                print("  failed: " + f)
        else:
            print("PASS: %s %s: %d checks, %d negative controls rejected" % (fid, title, fam.checks,
                                                                            len(fam.controls)))
            for s in fam.scope:
                print("  scope: " + s)
            for cid, desc in fam.controls:
                print("  control %s rejected: %s" % (cid, desc))
        total_checks += fam.checks
        total_controls += len(fam.controls)
    if failed:
        print("RESULT: FAIL %s: %d of %d families failed" % (NAME, failed, len(FAMILIES)))
        return 1
    print("RESULT: PASS %s: %d checks, %d negative controls rejected" % (NAME, total_checks, total_controls))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
