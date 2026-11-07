#!/usr/bin/env python3
"""Exact finite cross-checks of the algebra of Appendix A of
"A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices".

Python standard library only; exact integer, rational and Gaussian-rational
arithmetic. Square and 2^k-th roots enter only through rational brackets that
are verified by exact squaring at every step; eigenvalues of matrices with
irrational spectra enter only through exact Sturm (Sylvester inertia)
bisection brackets. The data are fixed (SHA-256 counter-mode generator), so
the output is deterministic. Every check family runs negative controls; the
run fails if a control is accepted.

Locators refer to the numbering printed in the final version of the paper:
Appendix A, its recurrence for P(z) = det(zI + 2I + A), the Graeffe transform
G(P)(z) = E(-z)^2 + z O(-z)^2, the bounds p_j <= e_j <= 2^n p_j, (43), and the
index-wise matching lambda^_j = r^_{n+1-j} - 2.

Usage:  python3 -S -s -B check_appendix_a.py [--inject-fault]
Exit status 0 and final line "RESULT: PASS check_appendix_a.py: ..." on success.
"""

import sys
import hashlib
import itertools
from fractions import Fraction as Q
from math import isqrt, comb, lcm

NAME = "check_appendix_a.py"
HALF = Q(1, 2)
ROOT_BITS = 128
FAULT = [False]


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


# ---------------------------------------------------------------- polynomials (ascending coefficients)

def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    m = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(m)])


def psub(p, q):
    m = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(m)])


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a != 0:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return ptrim(r)


def pscale(c, p):
    return ptrim([c * a for a in p])


def peval(p, x):
    acc = 0
    for c in reversed(p):
        acc = acc * x + c
    return acc


def peq(p, q):
    p, q = ptrim(p), ptrim(q)
    return len(p) == len(q) and ALL(EQ(a, b) for a, b in zip(p, q))


def from_roots(rs):
    P = [1]
    for r in rs:
        P = pmul(P, [r, 1])
    return P


def interpolate(xs, ys):
    P = [Q(0)]
    for i in range(len(xs)):
        L, den = [Q(1)], Q(1)
        for j in range(len(xs)):
            if j != i:
                L = pmul(L, [-xs[j], Q(1)])
                den *= xs[i] - xs[j]
        P = padd(P, pscale(ys[i] / den, L))
    return P


def continuant(a, c, shift, sign=-1):
    """Appendix A: P_0 = 1, P_1 = z + shift + a_1, P_i = (z + shift + a_i) P_{i-1} - c_{i-1} P_{i-2} (sign = -1)."""
    n = len(a)
    if n == 0:
        return [1]
    P0, P1 = [1], [shift + a[0], 1]
    for i in range(1, n):
        P0, P1 = P1, padd(pmul([shift + a[i], 1], P1), pscale(sign * c[i - 1], P0))
    return P1


def split_even_odd(P):
    return P[0::2], P[1::2]


def graeffe(P, variant=0):
    """G(P)(z) = E(-z)^2 + z O(-z)^2 (variant 0); variants 1, 2 are the wrong-sign controls."""
    E, O = split_even_odd(P)
    if variant == 1:                       # E(z)^2 - z O(z)^2
        return psub(pmul(E, E), [0] + pmul(O, O))
    Em = [e if k % 2 == 0 else -e for k, e in enumerate(E)]
    Om = [o if k % 2 == 0 else -o for k, o in enumerate(O)]
    if variant == 2:                       # E(-z)^2 - z O(-z)^2
        return psub(pmul(Em, Em), [0] + pmul(Om, Om))
    return padd(pmul(Em, Em), [0] + pmul(Om, Om))


def elem_sym(s, j):
    return sum((_prod(c) for c in itertools.combinations(s, j)), 0)


def _prod(xs):
    r = 1
    for x in xs:
        r = r * x
    return r


# ---------------------------------------------------------------- determinants

def det_q(A):
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


class GQ:
    """Gaussian rational re + i im."""
    __slots__ = ("re", "im")

    def __init__(self, re, im=0):
        self.re, self.im = Q(re), Q(im)

    def __add__(self, o):
        return GQ(self.re + o.re, self.im + o.im)

    def __sub__(self, o):
        return GQ(self.re - o.re, self.im - o.im)

    def __mul__(self, o):
        return GQ(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def __truediv__(self, o):
        d = o.re * o.re + o.im * o.im
        if d == 0:
            raise ZeroDivisionError("division by zero")
        return GQ((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)

    def __neg__(self):
        return GQ(-self.re, -self.im)

    def conj(self):
        return GQ(self.re, -self.im)

    def iszero(self):
        return self.re == 0 and self.im == 0


def det_g(A):
    M = [list(r) for r in A]
    n = len(M)
    d = GQ(1)
    for c in range(n):
        p = None
        for r in range(c, n):
            if not M[r][c].iszero():
                p = r
                break
        if p is None:
            return GQ(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d = d * M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if not f.iszero():
                for k in range(c, n):
                    M[r][k] = M[r][k] - f * M[c][k]
    return d


def det_leibniz_poly(Mp):
    """Determinant of a matrix of polynomials by the permutation expansion (independent of the recurrence)."""
    n = len(Mp)
    total = [0]
    for perm in itertools.permutations(range(n)):
        term = [1]
        for i in range(n):
            e = Mp[i][perm[i]]
            if ptrim(e) == [0]:
                term = None
                break
            term = pmul(term, e)
        if term is None:
            continue
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
        total = padd(total, term) if inv % 2 == 0 else psub(total, term)
    return total


# ---------------------------------------------------------------- roots and eigenvalue brackets

def sqrt_hi(x, bits=8):
    x = Q(x)
    a = isqrt((x.numerator << (2 * bits)) // x.denominator)
    hi = Q(a + 1, 1 << bits)
    if not (x < hi * hi):
        raise ArithmeticError("square-root bracket failed")
    return hi


def root2k_bracket(num, den, k, b=ROOT_BITS):
    """Rationals lo <= (num/den)^(1/2^k) <= hi, from k successive square roots, each verified by exact squaring."""
    if num <= 0 or den <= 0:
        raise ValueError("positive ratio required")
    if k == 0:
        return Q(num, den), Q(num, den)
    shifted = num << (2 * b)
    L = isqrt(shifted // den)
    H = L + 1
    if not (L * L * den <= shifted and H * H * den > shifted):
        raise ArithmeticError("first square root not bracketed")
    for _ in range(k - 1):
        L2 = isqrt(L << b)
        H2 = isqrt(H << b) + 1
        if not (L2 * L2 <= (L << b) and H2 * H2 > (H << b)):
            raise ArithmeticError("square root not bracketed")
        L, H = L2, H2
    return Q(L, 1 << b), Q(H, 1 << b)


def sturm_count(a, c, x):
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


def eig_brackets(a, c, bits=100):
    n = len(a)
    bound = Q(2)
    if sturm_count(a, c, -bound) != 0 or sturm_count(a, c, bound) != n:
        raise ArithmeticError("spectrum not enclosed in (-2, 2)")
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


# ================================================================ A01

def fam_a01(F):
    """Appendix A: the recurrence P_i = (z + 2 + a_i) P_{i-1} - c_{i-1} P_{i-2} equals det(zI + 2I + A)."""
    rng = Rng("A01")
    real_insts = []
    for n in range(1, 9):
        for _ in range(6):
            a = [rng.rational(-1, 1, 8) for _ in range(n)]
            beta = [rng.rational(-1, 1, 8) if rng.below(5) else Q(0) for _ in range(n - 1)]
            real_insts.append((a, beta))

    def real_ok(a, beta, csq, sign=-1, perturb=Q(0)):
        n = len(a)
        c = [b * b for b in beta] if csq else list(beta)
        P = continuant(a, c, 2, sign)
        xs = [Q(k) for k in range(n + 1)] + [Q(-1, 3), Q(5, 2)]
        vals = []
        for x in xs:
            M = [[(x + 2 + a[i] + (perturb if i == 0 else 0)) if i == j else
                  (beta[min(i, j)] if abs(i - j) == 1 else Q(0)) for j in range(n)] for i in range(n)]
            vals.append(det_q(M))
        D = interpolate(xs[:n + 1], vals[:n + 1])
        return (peq(P, D) and len(ptrim(D)) == n + 1 and EQ(ptrim(D)[-1], 1)
                and ALL(EQ(peval(D, x), v) for x, v in zip(xs[n + 1:], vals[n + 1:])))

    csq = not FAULT[0]
    for a, beta in real_insts:
        F.ok(real_ok(a, beta, csq), "recurrence = det(zI + 2I + A) (Gaussian elimination and interpolation)")
    F.control("N1", "recurrence with c_i = beta_i instead of |beta_i|^2", ALL(real_ok(a, b, False) for a, b in real_insts))
    F.control("N2", "recurrence with + c_{i-1} P_{i-2}", ALL(real_ok(a, b, True, +1) for a, b in real_insts))
    F.control("N3", "determinant input perturbed (a_1 + 1/8)", ALL(real_ok(a, b, True, -1, Q(1, 8)) for a, b in real_insts))
    # Second, independent determinant: the permutation expansion of the polynomial matrix, n <= 7.
    cnt = 0
    for a, beta in real_insts:
        n = len(a)
        if n > 7:
            continue
        Mp = [[[2 + a[i], 1] if i == j else [beta[min(i, j)] if abs(i - j) == 1 else Q(0)] for j in range(n)]
              for i in range(n)]
        F.ok(peq(continuant(a, [b * b for b in beta], 2), det_leibniz_poly(Mp)), "recurrence = permutation expansion")
        cnt += 1
    # Complex Hermitian A: c_i = (Re A_{i,i+1})^2 + (Im A_{i,i+1})^2; det(xI + 2I + A) is real.
    cplx = []
    for n in range(1, 9):
        for _ in range(4):
            a = [rng.rational(-1, 1, 8) for _ in range(n)]
            beta = [GQ(rng.rational(-1, 1, 8), rng.nonzero(-1, 1, 8)) for _ in range(n - 1)]
            cplx.append((a, beta))

    def cplx_ok(a, beta, cfun):
        n = len(a)
        P = continuant(a, [cfun(b) for b in beta], 2)
        good = True
        for x in [Q(k) for k in range(n + 2)] + [Q(-7, 4)]:
            M = [[GQ(x + 2 + a[i]) if i == j else (beta[i] if j == i + 1 else (beta[j].conj() if i == j + 1 else GQ(0)))
                  for j in range(n)] for i in range(n)]
            d = det_g(M)
            good = good and EQ(d.im, 0) and EQ(d.re, peval(P, x))
        return good

    for a, beta in cplx:
        F.ok(cplx_ok(a, beta, lambda b: b.re * b.re + b.im * b.im), "complex Hermitian: c_i = Re^2 + Im^2, det real")
    F.control("N4", "complex Hermitian with c_i = Re^2 - Im^2", ALL(cplx_ok(a, b, lambda z: z.re * z.re - z.im * z.im)
                                                                    for a, b in cplx))
    # Scaled Kac (Clement) form: superdiagonal i/n, subdiagonal (n-i)/n; products c_i = i(n-i)/n^2.
    for n in range(2, 9):
        c = [Q(i * (n - i), n * n) for i in range(1, n)]
        P = continuant([Q(0)] * n, c, 2)
        xs = [Q(k) for k in range(n + 1)]
        vals = [det_q([[x + 2 if i == j else (Q(i + 1, n) if j == i + 1 else (Q(n - j - 1, n) if i == j + 1 else Q(0)))
                        for j in range(n)] for i in range(n)]) for x in xs]
        F.ok(peq(P, interpolate(xs, vals)), "Kac form: continuant with products of off-diagonal pairs")
    F.note("48 real symmetric instances (n = 1..8; %d also by permutation expansion), 32 complex Hermitian "
           "instances, 7 scaled Kac matrices" % cnt)


# ================================================================ A02

def fam_a02(F):
    """Appendix A: P(z) = E(z^2) + z O(z^2); G(P)(z) = E(-z)^2 + z O(-z)^2 = prod (z + r_j^2); k steps give r_j^(2^k)."""
    rng = Rng("A02")
    insts = []
    for n in range(1, 9):
        for _ in range(8):
            rs = [rng.rational(-4, 4, 16) for _ in range(n)]
            if n >= 2 and rng.below(3) == 0:
                rs[1] = rs[0]
            insts.append(rs)
    insts.append([Q(0), Q(3, 2), Q(3, 2), Q(-1)])
    for rs in insts:
        P = from_roots(rs)
        E, O = split_even_odd(P)
        rebuilt = [0] * len(P)
        for k, e in enumerate(E):
            rebuilt[2 * k] = e
        for k, o in enumerate(O):
            rebuilt[2 * k + 1] = o
        F.ok(peq(rebuilt, P), "P(z) = E(z^2) + z O(z^2)")
        n = len(rs)
        F.ok(ALL(EQ(P[n - j], elem_sym(rs, j)) for j in range(n + 1)), "coefficient of z^(n-j) is e_j(r)")
        G = P
        for k in range(1, 6 if n <= 6 else 4):
            G = graeffe(G)
            F.ok(peq(G, from_roots([r ** (2 ** k) for r in rs])) and EQ(G[-1], 1),
                 "k Graeffe steps give prod (z + r_j^(2^k)), monic")
    F.note("%d root lists (n = 1..8, mixed signs, zeros and ties), up to 5 Graeffe steps" % len(insts))
    F.control("N1", "G(P) = E(z)^2 - z O(z)^2 (sign convention for prod (z - r_j))",
              ALL(peq(graeffe(from_roots(rs), 1), from_roots([r * r for r in rs])) for rs in insts))
    F.control("N2", "G(P) = E(-z)^2 - z O(-z)^2", ALL(peq(graeffe(from_roots(rs), 2), from_roots([r * r for r in rs]))
                                                      for rs in insts))
    F.control("N3", "three steps give prod (z + r_j^6) (exponent 2k instead of 2^k)",
              ALL(peq(graeffe(graeffe(graeffe(from_roots(rs)))), from_roots([r ** 6 for r in rs])) for rs in insts))


# ================================================================ A03

def fam_a03(F):
    """Appendix A: for r_1 >= ... >= r_n > 0 and p_j = prod_{i<=j} r_i^R: p_j <= e_j <= C(n,j) p_j <= 2^n p_j and (43)."""
    rng = Rng("A03")
    insts = []
    for n in range(1, 9):
        for _ in range(8):
            rs = sorted((rng.rational(Q(1, 16), Q(63, 16), 16) for _ in range(n)), reverse=True)
            if n >= 3 and rng.below(2) == 0:
                rs[2] = rs[1]
            insts.append(rs)
    insts.append([Q(3)] * 5)
    insts.append([Q(7, 2), Q(7, 2), Q(1, 16), Q(1, 16)])

    def bounds(rs, k, upper_coef, use_order=True):
        n = len(rs)
        R = 2 ** k
        G = from_roots(rs)
        for _ in range(k):
            G = graeffe(G)
        e = [G[n - j] for j in range(n + 1)]
        order = rs if use_order else sorted(rs)
        p = [_prod([order[i] ** R for i in range(j)]) for j in range(n + 1)]
        res = [EQ(e[0], 1), ALL(GT(x, 0) for x in e)]
        res.append(ALL(LE(p[j], e[j]) and LE(e[j], upper_coef(n, j) * p[j]) and LE(comb(n, j), 2 ** n)
                       for j in range(n + 1)))
        res.append(ALL(LE(order[j - 1] ** R / 2 ** n, e[j] / e[j - 1]) and LE(e[j] / e[j - 1], 2 ** n * order[j - 1] ** R)
                       for j in range(1, n + 1)))
        res.append(ALL(EQ(e[j], elem_sym([r ** R for r in rs], j)) for j in range(n + 1)) if n <= 8 else True)
        return res

    for rs in insts:
        for k in range(0, 7):
            r = bounds(rs, k, lambda n, j: comb(n, j))
            F.ok(r[0] and r[1], "e_0 = 1 and e_j > 0")
            F.ok(r[2], "p_j <= e_j <= C(n,j) p_j <= 2^n p_j")
            F.ok(r[3], "(43) in R-th power form: r_j^R 2^-n <= e_j/e_{j-1} <= r_j^R 2^n")
            F.ok(r[4], "e_j = elementary symmetric function of r_i^R")
    F.note("%d decreasing root lists in (0, 4) (n = 1..8, with ties), R = 2^k for k = 0..6" % len(insts))
    F.control("N1", "upper bound p_j instead of 2^n p_j (e_j <= p_j)",
              ALL(bounds(rs, k, lambda n, j: 1)[2] for rs in insts for k in (0, 3)))
    F.control("N2", "roots labelled in increasing order", ALL(bounds(rs, 2, lambda n, j: comb(n, j), False)[3]
                                                             for rs in insts if len(set(rs)) > 1))
    F.control("N3", "C(n,j) - 1 instead of C(n,j) (equal roots attain C(n,j))",
              ALL(bounds([Q(3)] * 5, k, lambda n, j: max(comb(n, j) - 1, 1))[2] for k in (0, 2)))


# ================================================================ A04

def pipeline(a, c, eps, known=None, steps_delta=0, ratio_flip=False):
    """Appendix A on exact data. Returns (checks, err) where checks is a list of (label, bool) and err[j] is a
    rigorous upper bound on |lambda^_j - lambda_j| (0-based ascending j) when the index-wise matching is used."""
    n = len(a)
    out = []
    # ||A||_2 < 2 by Gershgorin (upper brackets of sqrt c_i), so r_j = 2 + lambda_{n+1-j} lies in (0, 4).
    rows = [abs(a[i]) + (sqrt_hi(c[i - 1]) if i > 0 else 0) + (sqrt_hi(c[i]) if i < n - 1 else 0) for i in range(n)]
    out.append(("||A||_2 < 2 (Gershgorin)", LT(max(rows), 2)))
    P = continuant(a, c, 2)
    Ls = 1
    for v in list(a) + list(c):
        Ls = lcm(Ls, Q(v).denominator)
    Pint = continuant([Ls * x for x in a], [Ls * Ls * x for x in c], 2 * Ls)
    out.append(("integer-scaled recurrence: coefficient m equals L^(n-m) P_m",
                ALL(EQ(Pint[m], Ls ** (n - m) * P[m]) and Q(Pint[m]).denominator == 1 for m in range(n + 1))))
    Pint = [int(x) for x in Pint]
    if known is not None:
        lam = sorted(known)
        r = [2 + lam[n - 1 - i] for i in range(n)]          # r_1 >= ... >= r_n
        out.append(("P(z) = prod (z + r_j) with r_j = 2 + lambda_{n+1-j}", peq(P, from_roots(r))))
        out.append(("r_1 >= ... >= r_n in (0, 4)", ALL(GE(r[i], r[i + 1]) for i in range(n - 1))
                    and ALL(LT(0, x) and LT(x, 4) for x in r)))
    sj = sum(range(1, n + 1))
    eta = eps / sj
    R, k = 1, 0
    while R * eta < 8 * n:
        R, k = 2 * R, k + 1
    out.append(("R = 2^k least with R eta >= 8n; n <= R; 4n/R <= eta/2",
                GE(R * eta, 8 * n) and LT(R * eta / 2, 8 * n) and n <= R and LE(Q(4 * n, R), eta / 2)))
    G = Pint
    for _ in range(k + steps_delta):
        G = graeffe(G)
    e = [G[n - j] for j in range(n + 1)]
    out.append(("e_0 = 1 and e_j > 0", e[0] == 1 and ALL(x > 0 for x in e)))
    rhat = []
    for j in range(1, n + 1):
        num, den = (e[j - 1], e[j]) if ratio_flip else (e[j], e[j - 1])
        lo, hi = root2k_bracket(num, den, k)
        rhat.append((lo / Ls, hi / Ls))
    if known is not None:
        good43, goodr = True, True
        for j in range(1, n + 1):
            u = Ls * r[j - 1]                                 # (L r_j)^R compared with e_j/e_{j-1}
            un, ud = u.numerator, u.denominator
            good43 = good43 and (e[j] * ud ** R * 2 ** n >= un ** R * e[j - 1]) and (e[j] * ud ** R <= 2 ** n * un ** R * e[j - 1])
            lo, hi = rhat[j - 1]
            goodr = goodr and LE(hi - r[j - 1], Q(4 * n, R)) and LE(r[j - 1] - lo, Q(4 * n, R))
        out.append(("(43) in R-th power form", good43))
        out.append(("|r^_j - r_j| <= 4n/R", goodr))
        lam_br = [(x, x) for x in lam]
    else:
        lam_br = eig_brackets(a, c)
    err = []
    for j in range(n):
        lo, hi = rhat[n - 1 - j]                              # lambda^_j = r^_{n+1-j} - 2 (1-based)
        err.append(max(hi - 2 - lam_br[j][0], lam_br[j][1] - (lo - 2)))
    out.append(("|lambda^_j - lambda_j| <= eta/2 (index-wise matching)", ALL(LE(x, eta / 2) for x in err)))
    out.append(("|sum j lambda^_j - sum j lambda_j| <= eps", LE(sum(((j + 1) * err[j] for j in range(n)), Q(0)), eps)))
    unrev = []
    for j in range(n):
        lo, hi = rhat[j]
        unrev.append(max(hi - 2 - lam_br[j][0], lam_br[j][1] - (lo - 2)))
    return out, err, unrev, eta, R


def fam_a04(F):
    """Appendix A pipeline: doubling for R, k Graeffe steps, R-th roots by k square roots, lambda^_j = r^_{n+1-j} - 2."""
    rng = Rng("A04")
    eps_cycle = [Q(1, 2), Q(9, 10), Q(1, 3)]
    insts = []
    for n in range(2, 9):                                    # scaled Clement matrices, spectrum (2k - n + 1)/n
        c = [Q(i * (n - i), n * n) for i in range(1, n)]
        lam = [Q(2 * k - n + 1, n) for k in range(n)]
        insts.append(("Clement", [Q(0)] * n, c, lam))
        insts.append(("shifted Clement", [Q(1, 3)] * n, c, [x + Q(1, 3) for x in lam]))
    for n in (4, 5, 6, 8):                                   # Pythagorean blocks, repeated eigenvalues
        a, c, lam = [], [], []
        blk = (rng.rational(-HALF, HALF, 8), rng.nonzero(-Q(1, 8), Q(1, 8), 16))
        while len(a) < n:
            if a:
                c.append(Q(0))
            if n - len(a) >= 2 and rng.below(4):
                m, s = blk if rng.below(2) else (rng.rational(-HALF, HALF, 8), rng.nonzero(-Q(1, 8), Q(1, 8), 16))
                a += [m + 3 * s, m - 3 * s]
                c.append((4 * s) ** 2)
                lam += [m + 5 * s, m - 5 * s]
            else:
                m = blk[0]
                a.append(m)
                lam.append(m)
        insts.append(("Pythagorean blocks", a, c, lam))
    for n in (3, 6):                                         # diagonal with ties
        a = [rng.rational(-1, 1, 4) for _ in range(n)]
        a[1] = a[0]
        insts.append(("diagonal", a, [Q(0)] * (n - 1), list(a)))
    for n in range(2, 7):                                    # generic rational tridiagonal: Sturm brackets
        for _ in range(2):
            a = [rng.rational(-Q(3, 4), Q(3, 4), 8) for _ in range(n)]
            b = [rng.nonzero(-HALF, HALF, 8) for _ in range(n - 1)]
            insts.append(("generic", a, [x * x for x in b], None))
    unrev_bad = []
    flip_bad = []
    rmax, nrep = 0, 0
    for idx, (kind, a, c, lam) in enumerate(insts):
        eps = eps_cycle[idx % 3]
        out, err, unrev, eta, R = pipeline(a, c, eps, lam)
        rmax = max(rmax, R)
        nrep += 1 if (lam is not None and len(set(lam)) < len(lam)) else 0
        for label, v in out:
            F.ok(v, kind + ": " + label)
        if lam is None or len(set(lam)) > 1:
            unrev_bad.append(ALL(LE(x, eta / 2) for x in unrev))
        if idx % 4 == 0 and len(a) <= 6:
            o2, e2, _, eta2, _ = pipeline(a, c, eps, lam, ratio_flip=True)
            flip_bad.append(ALL(v for _, v in o2))
    F.note("%d instances: scaled and shifted Clement (n = 2..8), Pythagorean blocks, diagonal with ties "
           "(%d instances with a repeated eigenvalue), and 10 generic rational matrices (n = 2..6) with exact "
           "Sturm brackets; eps in {1/2, 9/10, 1/3}, R up to 2^%d" % (len(insts), nrep, rmax.bit_length() - 1))
    F.control("N1", "matching without index reversal (lambda^_j = r^_j - 2)", ALL(unrev_bad))
    F.control("N2", "ratio e_{j-1}/e_j instead of e_j/e_{j-1}", ALL(flip_bad))
    lam = [Q(2 * k - 5 + 1, 5) for k in range(5)]
    c5 = [Q(i * (5 - i), 25) for i in range(1, 5)]
    o3 = pipeline([Q(0)] * 5, c5, Q(1, 2), lam, steps_delta=-1)[0]
    F.control("N3", "one Graeffe step fewer than k with the same R-th root", ALL(v for _, v in o3))


# ================================================================ driver

FAMILIES = [
    ("A01", "Appendix A recurrence = det(zI + 2I + A) [real symmetric, complex Hermitian, Kac]", fam_a01),
    ("A02", "Appendix A even/odd split and Graeffe steps [prod (z + r_j^(2^k))]", fam_a02),
    ("A03", "Appendix A coefficient bounds, (43) [p_j <= e_j <= 2^n p_j, ratio bounds]", fam_a03),
    ("A04", "Appendix A pipeline, Lemma 4.3 [R >= 8n/eta, k square roots, lambda^_j = r^_{n+1-j} - 2]", fam_a04),
]


def main(argv):
    FAULT[0] = False
    if argv == ["--inject-fault"]:
        FAULT[0] = True
    elif argv:
        print("FAIL: usage: check_appendix_a.py [--inject-fault]")
        return 2
    if sys.version_info < (3, 11):
        print("FAIL: Python 3.11 or later is required")
        return 1
    print("== %s: KE-02 exact checks of the Appendix A algebra ==" % NAME)
    print("exact integer/rational/Gaussian-rational arithmetic only; finite cross-checks on fixed data")
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
