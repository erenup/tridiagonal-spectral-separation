#!/usr/bin/env python3
"""Corrupt complex-edge and center data while preserving input consistency."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise SystemExit('FAIL: additional control: ' + message)


def save(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    need(not args.work.exists(), 'work directory must be new')
    args.work.mkdir(parents=True)
    cases = [
        ('remove_imaginary_edge_with_consistent_binding', 'complex2',
         'ENCLOSURE_UPPER', 'FAIL[ENCLOSURE_UPPER]: minus eigenvalue 1\n'),
        ('zero_center_with_consistent_diagonal', 'zero2',
         'OUTPUT_RANGE', 'FAIL[OUTPUT_RANGE]: c±r must lie in [0,β]\n'),
    ]
    records = []
    for name, fixture, reason, expected in cases:
        data = json.loads((HERE / 'fixtures' / (fixture + '.json')).read_text())
        cert = json.loads((HERE / 'certificates' / (fixture + '.json')).read_text())
        if name == 'remove_imaginary_edge_with_consistent_binding':
            need(data['edge_imag'][0] != 0, 'nonzero imaginary edge required')
            data['edge_imag'][0] = 0
            cert['input'] = copy.deepcopy(data)
        else:
            cert['center_grid'] = 0
            cert['diagonal_grid'] = [0] * data['n']
        ip = args.work / (name + '.input.json')
        cp = args.work / (name + '.certificate.json')
        save(ip, data)
        save(cp, cert)
        command = [sys.executable, '-P', '-S', '-s', '-B']
        if sys.flags.optimize:
            command.append('-O')
        command.extend([str(HERE / 'verify.py'), str(ip), str(cp)])
        result = subprocess.run(command, stdin=subprocess.DEVNULL,
                                capture_output=True, timeout=120)
        need(result.returncode == 1, name + ': exit status')
        need(not result.stdout, name + ': unexpected standard output')
        need(result.stderr == expected.encode(), name + ': wrong rejection reason')
        records.append({'control': name, 'reason': reason})
    print(json.dumps({'status': 'PASS', 'negative_controls': records}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, subprocess.TimeoutExpired) as error:
        raise SystemExit('FAIL: additional control input: ' + type(error).__name__)
