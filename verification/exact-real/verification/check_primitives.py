#!/usr/bin/env python3
'Exact finite checks of continuants, Graeffe transforms and root ratios.\n\nAll decisive arithmetic uses integers and Fraction. These finite checks do\nnot establish the all-input theorem or its asymptotic operation count.\n'
import argparse
from fractions import Fraction as F
from itertools import permutations
from math import comb
import json


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def add(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return out


def multiply(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def direct_product(roots):
    p = [F(1)]
    for x in roots:
        p = multiply(p, [x, F(1)])
    return p


def graeffe(p, poison=False):
    even = [x * (-1)**i for i, x in enumerate(p[::2])]
    odd = [x * (-1)**i for i, x in enumerate(p[1::2])]
    a = multiply(even, even)
    b = [F(0)] + multiply(odd, odd)
    if poison:
        b = [-x for x in b]
    out = add(a, b)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def continuant(diagonal, edges, poison=False):
    pprev, p = [F(0)], [F(1)]
    for i, a in enumerate(diagonal):
        edge_square = edges[i-1]**2 if i else F(0)
        if poison:
            edge_square = -edge_square
        new = add(multiply(p, [2+a, F(1)]),
                  [-edge_square*x for x in pprev])
        pprev, p = p, new
    return p


def determinant_polynomial(diagonal, edges):
    n = len(diagonal)
    out = [F(0)]*(n+1)
    for perm in permutations(range(n)):
        inv = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1,n))
        term = [F((-1)**inv)]
        for i, j in enumerate(perm):
            entry = [2+diagonal[i], F(1)] if i == j else (
                [edges[min(i,j)]] if abs(i-j) == 1 else [F(0)])
            term = multiply(term, entry)
        out = add(out, term)
    return out


def check_ratios(roots, p, power, poison=False):
    n = len(roots)
    ordered = sorted(roots, reverse=True)
    elementary = list(reversed(p))
    products = [F(1)]
    for x in ordered:
        products.append(products[-1]*x**power)
    for j in range(n+1):
        require(products[j] <= elementary[j] <= comb(n,j)*products[j],
                'elementary symmetric coefficient sandwich')
    for j in range(1,n+1):
        ratio = elementary[j]/elementary[j-1]
        if poison:
            ratio = -ratio
        require(ratio > 0, 'positive repeated-square-root radicand')
        require(ordered[j-1]**power / (2**n) <= ratio <= ordered[j-1]**power * (2**n),
                'ratio matching bound')
        if power >= n:
            lower = ordered[j-1] * (1-F(n,power))
            upper = ordered[j-1] * (1+F(n,power))
            require(lower**power <= ratio <= upper**power,
                    'rational outward interval for the extracted root')


def reject(call, label):
    try:
        call()
    except SystemExit:
        return label
    raise SystemExit('FAIL: negative control accepted: '+label)


def main():
    diagonal_cases = [
        ([F(0),F(1,3)], [F(1,4)]),
        ([F(-1,2),F(1,5),F(1,2)], [F(0),F(-1,7)]),
        ([F(0),F(1,4),F(-1,3),F(1,6)], [F(1,3),F(1,8),F(-1,5)]),
    ]
    for diagonal, edges in diagonal_cases:
        require(continuant(diagonal,edges) == determinant_polynomial(diagonal,edges),
                'continuant vs independent permutation determinant')
    root_cases = [
        [F(1),F(3)],
        [F(1),F(1),F(1)],
        [F(1),F(2),F(2),F(3)],
        [F(4,3),F(3,2),F(5,3),F(8,3),F(3)],
        [F(1),F(1),F(3,2),F(2),F(3),F(3)],
    ]
    transformations = 0
    for roots in root_cases:
        p = direct_product(roots)
        power = 1
        for _ in range(7):
            require(p == direct_product([x**power for x in roots]),
                    'Graeffe output vs direct powered roots')
            require(all(x > 0 for x in p), 'strictly positive coefficients')
            check_ratios(roots,p,power)
            if power < 64:
                p = graeffe(p)
                power *= 2
                transformations += 1
    roots = [F(1),F(2),F(3)]
    p = direct_product(roots)
    negatives = [
        reject(lambda: require(graeffe(p,True) == direct_product([x*x for x in roots]),
                               'wrong Graeffe odd sign'), 'wrong Graeffe odd sign'),
        reject(lambda: require(continuant(*diagonal_cases[0],poison=True) ==
                               determinant_polynomial(*diagonal_cases[0]),
                               'wrong continuant coupling sign'), 'wrong coupling sign'),
        reject(lambda: check_ratios(roots,p,1,True), 'negative root ratio'),
        reject(lambda: require(80**4*16 < 10**8, 'false local-curvature constant'),
               'false local-curvature constant'),
    ]
    require(80**4*16 < 10**12, 'local-curvature constant')
    require(10**12 < 2**40, 'final universal constant')
    require(4096**4 == 2**48, 'radius fourth power')
    require(4*7+14 == 42, 'final dimension exponent')
    print(json.dumps(dict(continuant_cases=len(diagonal_cases),
                          root_families=len(root_cases),
                          graeffe_transformations=transformations,
                          coefficient_ratio_rounds=7*len(root_cases),
                          negative_controls=len(negatives),
                          scope='exact finite primitive checks; theorem is written'),
                     sort_keys=True))




def negative_control(name):
    roots = [F(1), F(2), F(3)]
    p = direct_product(roots)
    if name == 'graeffe-odd-sign':
        require(graeffe(p, True) == direct_product([x*x for x in roots]),
                'wrong Graeffe odd sign')
    elif name == 'continuant-coupling-sign':
        diagonal, edges = [F(0), F(1, 3)], [F(1, 4)]
        require(continuant(diagonal, edges, poison=True) ==
                determinant_polynomial(diagonal, edges), 'wrong continuant coupling sign')
    elif name == 'negative-root-ratio':
        check_ratios(roots, p, 1, True)
    elif name == 'curvature-constant':
        require(80**4*16 < 10**8, 'false local-curvature constant')
    else:
        raise SystemExit('FAIL: unknown negative control')
    raise SystemExit('FAIL: negative control unexpectedly passed')


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=['graeffe-odd-sign', 'continuant-coupling-sign', 'negative-root-ratio', 'curvature-constant'])
    args = parser.parse_args()
    if args.negative_control is not None:
        negative_control(args.negative_control)
    else:
        main()


if __name__ == '__main__':
    cli()
