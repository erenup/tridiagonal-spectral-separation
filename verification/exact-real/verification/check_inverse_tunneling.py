#!/usr/bin/env python3
'Exact finite checks of inverse-tunneling identities.\n\nOnly integers and Fraction are used. These checks cover identities, signs,\nboundary terms and constants. The all-input theorem uses the written proof.\n'
import argparse
from fractions import Fraction as Q


def need(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def dot(x, y):
    return sum((a*b for a, b in zip(x, y)), Q(0))


def det(x, y):
    return x[0]*y[1]-x[1]*y[0]


def transpose(a):
    return [list(row) for row in zip(*a)]


def mm(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def mv(a, v):
    return [dot(row, v) for row in a]


def add(a, b):
    return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    return [[c*x for x in row] for row in a]


def outer(u, v):
    return [[x*y for y in v] for x in u]


def eye(n):
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), Q(0))


def projector(row):
    norm2 = dot(row, row)
    need(norm2 > 0, 'nonzero projector row')
    return scale(1/norm2, outer(row, row))


def fixture():
    # An irreducible rational Jacobi matrix with a rational orthonormal
    # eigenbasis, independently checked by multiplication below.
    h = [[Q(0), Q(3, 5), Q(0)],
         [Q(3, 5), Q(7, 12), Q(4, 5)],
         [Q(0), Q(4, 5), Q(0)]]
    pairs = [(Q(4, 3), [Q(9, 25), Q(4, 5), Q(12, 25)]),
             (Q(-3, 4), [Q(-12, 25), Q(3, 5), Q(-16, 25)]),
             (Q(0), [Q(-4, 5), Q(0), Q(3, 5)])]
    for lam, u in pairs:
        need(mv(h, u) == [lam*x for x in u], 'rational eigenpair fixture')
    for i, (_, u) in enumerate(pairs):
        for j, (_, v) in enumerate(pairs):
            need(dot(u, v) == Q(i == j), 'orthonormal eigenpair fixture')
    return h, pairs


def check_rows(bad_wronskian=False, bad_projector=False, omit_error=False):
    base, pairs = fixture()
    count = 0
    for alpha, beta in [(Q(1), Q(0)), (Q(-1, 2), Q(2, 7)),
                        (Q(3, 5), Q(-1, 4))]:
        h = add(scale(alpha, base), scale(beta, eye(3)))
        for j in range(3):
            for k in range(j+1, 3):
                lam, u = alpha*pairs[j][0]+beta, pairs[j][1]
                mu, v = alpha*pairs[k][0]+beta, pairs[k][1]
                rows = list(zip(u, v))
                energy = (lam+mu)/2
                need(sum((det(rows[s], rows[t])**2
                          for s in range(3) for t in range(s+1, 3)), Q(0)) == 1,
                     'Cauchy--Binet identity')
                for i in range(2):
                    left = h[i][i+1]*det(rows[i], rows[i+1])
                    right = (mu-lam)*sum((u[z]*v[z] for z in range(i+1)), Q(0))
                    if bad_wronskian:
                        right = -right
                    need(left == right, 'Wronskian telescoping sign')
                for s in range(3):
                    for t in range(s+1, 3):
                        p = add(projector(rows[s]), scale(Q(-1), projector(rows[t])))
                        sine2 = det(rows[s], rows[t])**2 / (
                            dot(rows[s], rows[s])*dot(rows[t], rows[t]))
                        if bad_projector:
                            sine2 *= 2
                        need(mm(p, p) == scale(sine2, eye(2)),
                             'direction-projector squared identity')
                e = [(lam-energy)*rows[1][0], (mu-energy)*rows[1][1]]
                left = h[1][2]*det(rows[0], rows[2])
                right = (energy-h[1][1])*det(rows[0], rows[1])
                if not omit_error:
                    right += det(rows[0], e)
                need(left == right, 'distance-two recurrence and residual row')
                count += 1
    return count


def check_boundary(omit_outside=False):
    h, pairs = fixture()
    energy, w = pairs[0]
    n = len(w)
    for cut in (1, 2):
        p = [[Q(i == j and i < cut) for j in range(n)] for i in range(n)]
        comm = add(mm(h, p), scale(Q(-1), mm(p, h)))
        actual = mv(comm, w)
        expected = [Q(0)]*n
        expected[cut-1] = -h[cut-1][cut]*w[cut]
        if not omit_outside:
            expected[cut] = h[cut-1][cut]*w[cut-1]
        need(actual == expected, 'both full commutator boundary components')
        norm2 = h[cut-1][cut]**2 * (w[cut-1]**2+w[cut]**2)
        need(dot(actual, actual) == norm2, 'exact boundary norm square')
        a = add(h, scale(-energy, eye(n)))
        need(mv(a, mv(p, w)) == [x+y for x, y in zip(mv(p, mv(a, w)), actual)],
             'full truncation residual identity')


def check_flatten(bad_expansion=False, bad_swap=False):
    f = [Q(3, 5), Q(4, 5), Q(0), Q(0)]
    g = [Q(0), Q(0), Q(5, 13), Q(12, 13)]
    fp = [Q(-4, 5), Q(3, 5), Q(0), Q(0)]
    gp = [Q(0), Q(0), Q(-12, 13), Q(5, 13)]
    basis = [fp, f, g, gp]
    for i, u in enumerate(basis):
        for j, v in enumerate(basis):
            need(dot(u, v) == Q(i == j), 'flattening orthonormal fixture')
    h = [[Q(1, 7), Q(1, 3), Q(0), Q(0)],
         [Q(1, 3), Q(-2, 5), Q(3, 8), Q(0)],
         [Q(0), Q(3, 8), Q(1, 9), Q(2, 7)],
         [Q(0), Q(0), Q(2, 7), Q(-1, 4)]]
    energy = Q(1, 11)
    q = add(outer(f, f), outer(g, g))
    qc = add(eye(4), scale(Q(-1), q))
    a = add(mm(mm(qc, h), qc), scale(energy, q))
    for v in (f, g):
        need(mv(a, v) == [energy*x for x in v], 'exact flattened eigenvector')
    residual = mm(add(h, scale(-energy, eye(4))), q)
    rhs = add(residual, transpose(residual))
    if not bad_expansion:
        rhs = add(rhs, scale(Q(-1), mm(q, residual)))
    need(add(h, scale(Q(-1), a)) == rhs, 'flattening expansion')
    norms2 = sum((dot(mv(add(h, scale(-energy, eye(4))), v),
                      mv(add(h, scale(-energy, eye(4))), v)) for v in (f, g)), Q(0))
    need(trace(mm(transpose(residual), residual)) == norms2,
         'rank-two residual Frobenius norm')

    exact = add(scale(Q(-2), outer(fp, fp)), scale(Q(2), outer(gp, gp)))
    plus = [[Q(0)]*4 for _ in range(4)]
    minus = [[Q(0)]*4 for _ in range(4)]
    for weight, v in zip((1, 2, 3, 4), basis):
        plus = add(plus, scale(Q(weight), outer(v, v)))
    for weight, v in zip((1, 3, 2, 4), basis):
        minus = add(minus, scale(Q(weight), outer(v, v)))
    need(trace(mm(exact, plus)) == 6 == trace(mm(exact, minus)),
         'equal maximizing trace at repeated eigenvalue')
    x = [[Q(i+1 if i == j else 0) for j in range(4)] for i in range(4)]
    slope = trace(mm(x, add(plus, scale(Q(-1), minus))))
    expected = dot(g, mv(x, g))-dot(f, mv(x, f))
    if bad_swap:
        expected = -expected
    need(slope == expected and expected >= 1, 'ordered support slope separation')


def check_constants(bad_threshold=False):
    need(2 < Q(3, 2)**2 and 18 < 25, 'square-root rational majorants')
    need(Q(5, 16) < 1, 'projector-chain contradiction factor')
    denominator = 10**8 if bad_threshold else 10**10
    need(80**4*16 < denominator, 'fourth-power curvature threshold')
    need(10**10 >= 256, 'local small-h range from r<=1, n>=2')
    need(4096**4 == 2**48 and 10**12 < 2**40, 'final gap constant')
    need(4*7+14 == 42, 'final gap exponent')


def reject(action, name):
    try:
        action()
    except SystemExit:
        return
    raise SystemExit('FAIL: negative control accepted: ' + name)


def main():
    count = check_rows()
    check_boundary()
    check_flatten()
    check_constants()
    reject(lambda: check_rows(bad_wronskian=True), 'reversed Wronskian sign')
    reject(lambda: check_rows(bad_projector=True), 'wrong projector norm')
    reject(lambda: check_rows(omit_error=True), 'missing skipped-row residual')
    reject(lambda: check_boundary(omit_outside=True), 'omitted outside leakage')
    reject(lambda: check_flatten(bad_expansion=True), 'missing overlap correction')
    reject(lambda: check_flatten(bad_swap=True), 'reversed maximizing-weight swap')
    reject(lambda: check_constants(bad_threshold=True), 'overstrong gap threshold')
    print('PASS: %d rational eigenpair cases, exact Wronskian/projector/skipped-row identities' % count)
    print('PASS: both truncation boundary terms, flattening, residual norm and spectral-weight swap')
    print('PASS: exact all-n constant comparisons; 7 negative controls rejected')




def negative_control(name):
    if name == 'wronskian-sign':
        check_rows(bad_wronskian=True)
    elif name == 'projector-norm':
        check_rows(bad_projector=True)
    elif name == 'skipped-row-residual':
        check_rows(omit_error=True)
    elif name == 'outside-leakage':
        check_boundary(omit_outside=True)
    elif name == 'flattening-overlap':
        check_flatten(bad_expansion=True)
    elif name == 'weight-swap':
        check_flatten(bad_swap=True)
    elif name == 'gap-threshold':
        check_constants(bad_threshold=True)
    else:
        raise SystemExit('FAIL: unknown negative control')
    raise SystemExit('FAIL: negative control unexpectedly passed')


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=['wronskian-sign', 'projector-norm', 'skipped-row-residual', 'outside-leakage', 'flattening-overlap', 'weight-swap', 'gap-threshold'])
    args = parser.parse_args()
    if args.negative_control is not None:
        negative_control(args.negative_control)
    else:
        main()


if __name__ == '__main__':
    cli()
