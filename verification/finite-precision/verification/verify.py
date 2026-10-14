#!/usr/bin/env python3
"""Independent exact rational spectral-enclosure verifier; no generator imports."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def need(condition, code, detail):
    if not condition:
        raise SystemExit(f'FAIL[{code}]: {detail}')


def unique(items):
    result = {}
    for key, value in items:
        need(key not in result, 'JSON_DUPLICATE', key)
        result[key] = value
    return result


def bad_number(value):
    raise SystemExit('FAIL[JSON_NUMBER]: non-integer JSON number '+value)


def load(path):
    try:
        return json.loads(Path(path).read_text(), object_pairs_hook=unique,
                          parse_float=bad_number, parse_constant=bad_number)
    except (OSError, UnicodeError, ValueError) as error:
        raise SystemExit('FAIL[JSON_SYNTAX]: '+str(error))


def fields(obj, keys, code):
    need(type(obj) is dict and set(obj) == set(keys), code, 'object field set')


def integer(x, code, detail):
    need(type(x) is int, code, detail)


def exact_inertia(diagonal, squares, shift=Fraction(0)):
    """Return (negative,zero,positive); exact congruences with 1x1/2x2 pivots.

    At a zero pivot with a nonzero adjacent edge, the 2x2 determinant is
    negative. Its inverse's lower-right entry is zero, so removing this
    block makes no change to the next diagonal.
    """
    work = [Fraction(x)-shift for x in diagonal]
    negative = zero = positive = 0
    i = 0
    while i < len(work):
        pivot = work[i]
        if pivot:
            if pivot < 0:
                negative += 1
            else:
                positive += 1
            if i+1 < len(work):
                work[i+1] -= squares[i]/pivot
            i += 1
        elif i+1 == len(work) or squares[i] == 0:
            zero += 1
            i += 1
        else:
            negative += 1
            positive += 1
            i += 2
    return negative, zero, positive


def exponent_at_least(target):
    power, exponent = 1, 0
    while power < target:
        power *= 2
        exponent += 1
    return exponent


def verify(data, cert):
    fields(data, ['schema', 'n', 'd', 'diagonal', 'edge_real', 'edge_imag'], 'INPUT_SCHEMA')
    need(data['schema'] == 'KE02.input.v1', 'INPUT_SCHEMA', 'schema tag')
    n, d = data['n'], data['d']
    integer(n, 'INPUT_INT', 'n'); integer(d, 'INPUT_INT', 'd')
    need(n >= 2 and d >= 2, 'INPUT_RANGE', 'n,d must be at least two')
    for name, size in [('diagonal', n), ('edge_real', n-1), ('edge_imag', n-1)]:
        need(type(data[name]) is list and len(data[name]) == size, 'INPUT_SHAPE', name)
        for value in data[name]:
            integer(value, 'INPUT_INT', name)
    fields(cert, ['schema', 'input', 'parameters', 'center_grid', 'diagonal_grid',
                  'intervals', 'defect_num', 'defect_den'], 'CERT_SCHEMA')
    need(cert['schema'] == 'KE02.certificate.v1', 'CERT_SCHEMA', 'schema tag')
    # Validate the embedded object independently before equality: bool == 1 is
    # true in Python, but booleans are not accepted as integer coefficients.
    fields(cert['input'], list(data), 'INPUT_BINDING')
    for key in ['n', 'd']:
        integer(cert['input'][key], 'INPUT_BINDING', 'embedded '+key)
    for key in ['diagonal', 'edge_real', 'edge_imag']:
        need(type(cert['input'][key]) is list, 'INPUT_BINDING', 'embedded '+key)
        for value in cert['input'][key]:
            integer(value, 'INPUT_BINDING', 'embedded coefficient')
    need(cert['input'] == data, 'INPUT_BINDING', 'certificate is for a different supplied proxy')
    a = exponent_at_least(4*n*(2**d))
    K = exponent_at_least(16*n*n*n)
    m = exponent_at_least(n*n)
    p = a+2*K+20+m
    Q = 2**p
    beta = Q//(2**a)
    ell = beta//(4**K)
    radius = Fraction(ell, 4)
    parameters = cert['parameters']
    expected = {'a': a, 'K': K, 'm': m, 'p': p, 'Q': Q, 'delta_den': 2**d,
                'beta_grid': beta, 'ell_grid': ell, 'radius_grid': radius}
    fields(parameters, expected, 'PARAM_SCHEMA')
    for key in expected:
        integer(parameters[key], 'PARAM_INT', key)
        code = ('PARAM_PRECISION' if key in ['p', 'Q'] else
                'PARAM_RADIUS' if key == 'radius_grid' else
                'PARAM_BUDGET' if key == 'delta_den' else 'PARAM_FORMULA')
        need(parameters[key] == expected[key], code, key)
    for key in ['diagonal', 'edge_real', 'edge_imag']:
        need(all(abs(v) <= Q+1 for v in data[key]), 'INPUT_MAGNITUDE', key)
    diagonal = [Fraction(v, Q) for v in data['diagonal']]
    squares = [Fraction(b*b+z*z, Q*Q) for b, z in zip(data['edge_real'], data['edge_imag'])]
    norm_bound = 1+Fraction(5, Q)
    need(exact_inertia(diagonal, squares, -norm_bound)[0] == 0 and
         exact_inertia(diagonal, squares, norm_bound)[2] == 0,
         'PROXY_NORM', 'proxy norm exceeds the necessary 1+5η bound')
    center = cert['center_grid']
    integer(center, 'OUTPUT_INT', 'center')
    output = cert['diagonal_grid']
    need(type(output) is list and len(output) == n, 'OUTPUT_SHAPE', 'diagonal')
    for value in output:
        integer(value, 'OUTPUT_INT', 'diagonal')
    need(output == [j*center for j in range(1, n+1)], 'OUTPUT_DIAGONAL', 'D must equal cX')
    need(0 <= n*center and Fraction(n*center, Q) <= Fraction(1, 4*(2**d)),
         'OUTPUT_BUDGET', '0≤nc≤δ/4')
    need(radius <= center <= beta-radius, 'OUTPUT_RANGE', 'c±r must lie in [0,β]')
    sets = cert['intervals']
    fields(sets, ['minus', 'center', 'plus'], 'INTERVAL_SCHEMA')
    values = {}
    for name, t in [('minus', center-radius), ('center', center), ('plus', center+radius)]:
        rows = sets[name]
        need(type(rows) is list and len(rows) == n, 'INTERVAL_SHAPE', name)
        matrix_diag = [x+Fraction(j*t, Q) for j, x in enumerate(diagonal, 1)]
        lower = upper = Fraction(0)
        for j, pair in enumerate(rows, 1):
            need(type(pair) is list and len(pair) == 2, 'INTERVAL_SHAPE', name)
            lo, hi = pair
            integer(lo, 'INTERVAL_INT', name); integer(hi, 'INTERVAL_INT', name)
            need(0 < hi-lo <= 7, 'INTERVAL_WIDTH', name)
            need(-2*Q <= lo < hi <= 2*Q, 'INTERVAL_RANGE', name)
            low_count = exact_inertia(matrix_diag, squares, Fraction(lo, Q))[0]
            high_count = exact_inertia(matrix_diag, squares, Fraction(hi, Q))[0]
            need(low_count < j, 'ENCLOSURE_LOWER', f'{name} eigenvalue {j}')
            need(high_count >= j, 'ENCLOSURE_UPPER', f'{name} eigenvalue {j}')
            lower += j*Fraction(lo, Q)
            upper += j*Fraction(hi, Q)
        values[name] = lower, upper
    W = n*(n+1)//2
    bound = values['plus'][1]+values['minus'][1]-2*values['center'][0]+Fraction(20*W, Q)
    integer(cert['defect_num'], 'DEFECT_INT', 'numerator')
    integer(cert['defect_den'], 'DEFECT_INT', 'denominator')
    need(cert['defect_den'] == Q, 'DEFECT_DENOMINATOR', 'bound denominator must equal Q')
    need(Fraction(cert['defect_num'], Q) == bound, 'DEFECT_FORMULA', 'declared B differs from recomputed B')
    r = Fraction(radius, Q)
    need(bound < r/2, 'DEFECT_SMALL', 'actual rational B is not less than r/2')
    gap_bound = r**4/Fraction(10**12*n**14)
    claimed_bound = Fraction(1, (2**100)*(2**(4*d))*n**42)
    need(gap_bound > claimed_bound, 'GAP_CONSTANT', 'final strict lower-bound comparison')
    return {'status': 'PASS', 'n': n, 'd': d, 'p': p,
            'intervals_checked': 3*n, 'center': str(Fraction(center, Q)),
            'radius': str(r), 'defect_bound': str(bound),
            'defect_over_radius': str(bound/r),
            'gap_bound': str(gap_bound),
            'scope': 'uniform for every normalized Hermitian tridiagonal in the stated component enclosure'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(load(args.input), load(args.certificate)), sort_keys=True))


if __name__ == '__main__':
    main()
