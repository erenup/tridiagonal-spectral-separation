#!/usr/bin/env python3
"""Fixed-grid integer constructor for the finite-information KE-02 theorem."""
import argparse
import json
from pathlib import Path
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def fail(reason):
    raise SystemExit('FAIL[GENERATOR]: ' + reason)


def pairs(items):
    out = {}
    for k, v in items:
        if k in out:
            fail('duplicate JSON field')
        out[k] = v
    return out


def not_number(value):
    fail('non-integer JSON number: ' + value)


def read_input(path):
    try:
        data = json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                          parse_float=not_number, parse_constant=not_number)
    except (OSError, ValueError) as error:
        fail(str(error))
    keys = {'schema', 'n', 'd', 'diagonal', 'edge_real', 'edge_imag'}
    if type(data) is not dict or set(data) != keys or data['schema'] != 'KE02.input.v1':
        fail('input schema')
    if type(data['n']) is not int or data['n'] < 2:
        fail('n must be an integer at least two')
    if type(data['d']) is not int or data['d'] < 2:
        fail('d must be an integer at least two')
    for key, length in [('diagonal', data['n']), ('edge_real', data['n']-1),
                        ('edge_imag', data['n']-1)]:
        if type(data[key]) is not list or len(data[key]) != length:
            fail('factor shape: ' + key)
        if any(type(x) is not int for x in data[key]):
            fail('factor integer: ' + key)
    return data


def ceil_log2(x):
    return (x - 1).bit_length()


class Constructor:
    def __init__(self, data):
        self.data = data
        self.n, self.d = data['n'], data['d']
        self.a = self.d + ceil_log2(4 * self.n)
        self.K = ceil_log2(16 * self.n**3)
        self.m = ceil_log2(self.n**2)
        self.p = self.a + 2*self.K + 20 + self.m
        self.Q = 1 << self.p
        self.beta = 1 << (self.p-self.a)
        self.ell = 1 << (self.p-self.a-2*self.K)
        self.radius = self.ell // 4
        if any(abs(x) > self.Q+1 for key in ['diagonal', 'edge_real', 'edge_imag']
               for x in data[key]):
            fail('input exceeds necessary component bounds')
        self.edge_squares = [b*b+z*z for b, z in zip(data['edge_real'], data['edge_imag'])]
        self.stats = {'p': self.p, 'value_calls': 0, 'spectral_calls': 0,
                      'count_calls': 0, 'pivot_steps': 0, 'zero_replacements': 0,
                      'max_pivot_bits': 0, 'max_quotient_bits': 0,
                      'max_word_bits': 0}
        self.record(self.Q, self.beta, self.ell, self.radius, *self.edge_squares)

    def record(self, *values):
        self.stats['max_word_bits'] = max(self.stats['max_word_bits'],
                                           *(abs(v).bit_length() for v in values))

    def count(self, diagonal, shift):
        """The safeguarded construction; Python // is signed floor division."""
        self.stats['count_calls'] += 1
        negative = 0
        previous = 0
        for i, entry in enumerate(diagonal):
            quotient = self.edge_squares[i-1] // previous if i else 0
            pivot = entry - shift - quotient
            if pivot == 0:
                pivot = -1
                self.stats['zero_replacements'] += 1
            negative += int(pivot < 0)
            previous = pivot
            self.stats['pivot_steps'] += 1
            self.stats['max_pivot_bits'] = max(self.stats['max_pivot_bits'], abs(pivot).bit_length())
            self.stats['max_quotient_bits'] = max(self.stats['max_quotient_bits'], abs(quotient).bit_length())
            self.record(entry, shift, quotient, pivot)
        return negative

    def spectrum(self, t):
        self.stats['spectral_calls'] += 1
        diagonal = [a+(i+1)*t for i, a in enumerate(self.data['diagonal'])]
        self.record(*diagonal)
        result = []
        for j in range(1, self.n+1):
            low, high = -2*self.Q, 2*self.Q
            for _ in range(self.p):
                mid = (low+high) // 2
                count = self.count(diagonal, mid)
                if count >= j:
                    high = min(high, mid+1)
                else:
                    low = max(low, mid-1)
                self.record(low, high, low+high, mid)
            if not 0 < high-low <= 7:
                fail('bisection width invariant')
            result.append([low, high])
        return result

    def value_numerator(self, t):
        """Return numerator of the weighted midpoint value over denominator 2Q."""
        self.stats['value_calls'] += 1
        intervals = self.spectrum(t)
        value = sum(j*(low+high) for j, (low, high) in enumerate(intervals, 1))
        self.record(value)
        return value

    def potential_numerator(self, low, high):
        quarter = (high-low) // 4
        values = [self.value_numerator(t) for t in [high, high-quarter, low+quarter, low]]
        result = values[0]-values[1]-values[2]+values[3]
        self.record(result)
        return result

    def run(self):
        low, high = 0, self.beta
        for _ in range(self.K):
            quarter = (high-low) // 4
            left = (low+quarter, low+2*quarter)
            right = (low+2*quarter, low+3*quarter)
            lv = self.potential_numerator(*left)
            rv = self.potential_numerator(*right)
            low, high = left if lv <= rv else right
        if high-low != self.ell:
            fail('final interval width')
        center = (low+high) // 2
        sets = {name: self.spectrum(t) for name, t in
                [('minus', center-self.radius), ('center', center), ('plus', center+self.radius)]}
        lower_center = sum(j*pair[0] for j, pair in enumerate(sets['center'], 1))
        upper_minus = sum(j*pair[1] for j, pair in enumerate(sets['minus'], 1))
        upper_plus = sum(j*pair[1] for j, pair in enumerate(sets['plus'], 1))
        W = self.n*(self.n+1)//2
        bound = upper_plus+upper_minus-2*lower_center+20*W
        self.record(center, lower_center, upper_minus, upper_plus, bound)
        if not 2*bound < self.radius:
            fail('constructed certificate does not satisfy the strict defect inequality')
        return {'schema': 'KE02.certificate.v1', 'input': self.data,
                'parameters': {'a': self.a, 'K': self.K, 'm': self.m, 'p': self.p,
                               'Q': self.Q, 'delta_den': 1 << self.d,
                               'beta_grid': self.beta, 'ell_grid': self.ell,
                               'radius_grid': self.radius},
                'center_grid': center,
                'diagonal_grid': [(i+1)*center for i in range(self.n)],
                'intervals': sets, 'defect_num': bound, 'defect_den': self.Q}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--stats', type=Path)
    args = parser.parse_args()
    constructor = Constructor(read_input(args.input))
    certificate = constructor.run()
    args.output.write_text(json.dumps(certificate, sort_keys=True, indent=2)+'\n')
    if args.stats:
        args.stats.write_text(json.dumps(constructor.stats, sort_keys=True, indent=2)+'\n')
    print(json.dumps({'status': 'GENERATED', 'n': constructor.n, 'd': constructor.d,
                      **constructor.stats}, sort_keys=True))


if __name__ == '__main__':
    main()
