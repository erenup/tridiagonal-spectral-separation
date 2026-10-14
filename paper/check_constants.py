#!/usr/bin/env python3
"""Exact arithmetic ledger for the uniform proof's numerical constants."""
import argparse
from fractions import Fraction as F
import json


def need(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--negative-control', choices=('curvature', 'oracle_error', 'exponent'))
    args = parser.parse_args()
    curvature_denominator = 10 ** 8 if args.negative_control == 'curvature' else 10 ** 12
    value_error_denominator = 512 if args.negative_control == 'oracle_error' else 1024
    exponent = 41 if args.negative_control == 'exponent' else 42

    need(16 * 2 ** 4 == 256, 'tau upper bound fourth-power coefficient')
    need(F(5, 16) < 1, 'projection-chain contradiction')
    need(F(4) + F(1, 2) <= 5, 'skipped-row direction constant')
    need(F(2) < F(3, 2) ** 2, 'one-half plus sqrt-two below two')
    need(3 ** 2 * 2 < 5 ** 2, 'three sqrt-two below five')
    need(256 <= 10 ** 12 * 2 ** 8, 'local h range for n at least two')
    transfer_coefficient = 4 * 5 * 2
    need(transfer_coefficient == 40, 'convexity transfer coefficient')
    curvature_numerator = (2 * transfer_coefficient) ** 4 * 16
    need(curvature_numerator < curvature_denominator, 'local curvature threshold')
    need(curvature_numerator < 10 ** 10 < 10 ** 12, 'stronger inverse-checker threshold implies proof threshold')

    potential_error = F(4 * 4, value_error_denominator)
    need(potential_error == F(1, 64), 'four-value potential error budget')
    selector_error = 2 * potential_error
    need(selector_error == F(1, 32), 'selection two-error allowance')
    steady_error = selector_error / (1 - F(1, 2))
    need(steady_error == F(1, 16), 'selector geometric error sum')
    need(F(1, 16) + steady_error == F(1, 8), 'final potential upper bound')
    need(2 * 16 == 32 and 32 ** 2 == 1024, 'minimal-doubling and interval constants')
    need(4 * 1024 == 4096, 'final radius constant')
    need(1 + 2 * 3 == 7, 'final radius exponent')
    need(4 * 7 + 14 == exponent, 'final dimension exponent')
    need(4096 ** 4 == 2 ** 48, 'fourth-power radius constant')
    need(10 ** 12 < 2 ** 40, 'public universal constant')
    need(10 ** 12 * 4096 ** 4 < 2 ** 88, 'public gap denominator')

    need(F(3, 6) == F(1, 2), 'evaluator eigenvalue error')
    need(2 * F(1, 2) == 1, 'undoing matrix scaling')
    need(F(1, 2048) == F(1, 2) * F(1, 1024), 'weighted query error is half the allowance')
    need(2048 * 1024 == 2 ** 21, 'smallest-epsilon denominator constant')
    need(1 + 2 + 7 == 10, 'n-over-epsilon exponent')

    values = {
        'status': 'PASS',
        'curvature_numerator': curvature_numerator,
        'curvature_denominator': curvature_denominator,
        'curvature_ratio': str(F(curvature_numerator, curvature_denominator)),
        'transfer_coefficient': transfer_coefficient,
        'potential_error': str(potential_error),
        'selection_error': str(selector_error),
        'steady_selector_error': str(steady_error),
        'final_potential_threshold': '1/8',
        'radius_denominator': 4096,
        'radius_dimension_exponent': 7,
        'strong_gap_denominator': 10 ** 12 * 4096 ** 4,
        'public_gap_denominator': 2 ** 88,
        'gap_dimension_exponent': exponent,
        'query_weighted_error_divided_by_length': '1/2048',
        'query_allowance_divided_by_length': '1/1024',
        'n_over_epsilon_upper_constant': 2 ** 21,
        'n_over_epsilon_upper_n_exponent': 10,
        'scope': 'exact constant arithmetic; symbolic inequalities and uniform cost are justified in the written proof'
    }
    print(json.dumps(values, sort_keys=True))


if __name__ == '__main__':
    main()
