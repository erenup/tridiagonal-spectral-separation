#!/usr/bin/env python3
"""Verify source bindings, exact certificates, deterministic outputs and controls."""
import sys

# Inventory validation must run before any extra sibling module can be imported.
if __name__ == '__main__' and not sys.flags.safe_path:
    sys.path.pop(0)

import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
MODES = [('normal', [], '1'), ('optimized', ['-O'], '1'),
         ('hash-seed', [], '8675309')]
FIXTURES = ('boundary8', 'complex2', 'complex3', 'fractional_proxy3',
            'repeated4', 'strong4', 'strong8', 'weak4', 'zero2', 'zero3',
            'zero_edges8')
CODE_HASHES = {
    'generate.py': '76637ca64ce2494b1e10e2285a39c624c57dc460f52cfc36f3d4b6f0f83858f1',
    'verify.py': 'daa86e4b058cfcf6c41cb9a7ebaea31f2cfe7729a7743b92fe94fdd3d3b0d3e1',
    'run_tests.py': '034a3719196de359f0b70bbec67495c56b82d544c983a3c7213730c0069f4b7f',
}
SOURCE_HASHES = {
    'PROOF.md': '06de4b246319b41fabaf50d068059e039584e101dc5cd43fcea61e54a767dd72',
    'STATEMENT.md': '209553c8c02393d5308b278cc30c1c5708cceed0e147e8fbee00c56377affa64',
}
CONTROL_REASONS = {
    'altered_proxy': 'INPUT_BINDING', 'swapped_proxy': 'INPUT_BINDING',
    'lower_enclosure': 'ENCLOSURE_LOWER', 'upper_enclosure': 'ENCLOSURE_UPPER',
    'wide_interval': 'INTERVAL_WIDTH', 'false_defect_bound': 'DEFECT_FORMULA',
    'defect_denominator': 'DEFECT_DENOMINATOR', 'radius': 'PARAM_RADIUS',
    'precision': 'PARAM_PRECISION', 'budget': 'PARAM_BUDGET',
    'a_formula': 'PARAM_FORMULA', 'output_diagonal': 'OUTPUT_DIAGONAL',
    'output_budget': 'OUTPUT_BUDGET', 'bool_input': 'INPUT_INT',
    'bool_embedded': 'INPUT_BINDING', 'bool_precision': 'PARAM_INT',
    'bool_interval': 'INTERVAL_INT', 'unknown_field': 'CERT_SCHEMA',
    'float_json': 'JSON_NUMBER', 'nonfinite_json': 'JSON_NUMBER',
    'duplicate_input': 'JSON_DUPLICATE', 'duplicate_cert': 'JSON_DUPLICATE',
    'malformed_json': 'JSON_SYNTAX', 'proxy_norm': 'PROXY_NORM',
    'genuine_bad_center': 'DEFECT_SMALL',
}
EXTRA_REASONS = {
    'remove_imaginary_edge_with_consistent_binding': 'ENCLOSURE_UPPER',
    'zero_center_with_consistent_diagonal': 'OUTPUT_RANGE',
}
EXPECTED_FILES = set(CODE_HASHES) | {
    'run.py', 'check_controls.py', 'README.md', 'SOURCE_BINDINGS.txt',
    'NEGATIVE_CONTROLS.json', 'OUTPUT_HASHES.json', 'SHA256SUMS',
    'fixtures/SOURCES.json',
} | {folder + '/' + name + '.json'
     for folder in ('fixtures', 'certificates') for name in FIXTURES}
OUTPUT_NAMES = {'run_tests.stdout', 'run_tests.report', 'check_controls.stdout'} | {
    name + '.' + kind for name in FIXTURES for kind in ('generate', 'verify')} | {
    'negative.' + name for name in CONTROL_REASONS}


def need(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    result = {}
    for key, value in items:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def reject_number(value):
    raise SystemExit('FAIL: non-integer JSON number: ' + value)


def read_json(data):
    return json.loads(data, object_pairs_hook=pairs,
                      parse_float=reject_number, parse_constant=reject_number)


def inventory():
    need(HERE.is_dir() and not HERE.is_symlink(), 'verification directory')
    result = {}
    for path in HERE.rglob('*'):
        name = path.relative_to(HERE).as_posix()
        need(not path.is_symlink(), 'symbolic link: ' + name)
        if path.is_dir():
            need(name in {'fixtures', 'certificates'}, 'unexpected directory: ' + name)
        else:
            need(path.is_file(), 'non-regular file: ' + name)
            need(path.stat().st_size <= 4500000, 'file size: ' + name)
            result[name] = path.read_bytes()
    return result


def proof_inventory():
    directory = HERE.parent / 'proofs'
    need(directory.is_dir() and not directory.is_symlink(), 'proof directory')
    paths = list(directory.iterdir())
    need({p.name for p in paths} == set(SOURCE_HASHES), 'proof coverage')
    need(all(p.is_file() and not p.is_symlink() for p in paths), 'proof file type')
    return {p.name: digest(p.read_bytes()) for p in paths}


def validate_bindings(data):
    bound = {}
    for line in data.decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        parts = line.split()
        need(len(parts) == 3, 'source binding syntax')
        source, document, name = parts
        need(all(re.fullmatch('[0-9a-f]{64}', value) for value in (source, document)),
             'source binding digest syntax')
        need(name in SOURCE_HASHES and source == SOURCE_HASHES[name], 'source proof hash')
        need(name not in bound, 'duplicate proof binding')
        bound[name] = document
    need(bound == proof_inventory(), 'proof binding mismatch')
    return bound


def control_map(entries, label):
    need(type(entries) is list, 'control list: ' + label)
    result = {}
    for entry in entries:
        need(type(entry) is dict and set(entry) == {'control', 'reason'},
             'control fields: ' + label)
        name, reason = entry['control'], entry['reason']
        need(type(name) is str and type(reason) is str, 'control strings: ' + label)
        need(name not in result, 'duplicate control: ' + label)
        result[name] = reason
    return result


def validate_controls(data):
    controls = read_json(data)
    need(type(controls) is dict and set(controls) == {'run_tests.py', 'check_controls.py'},
         'control registry coverage')
    need(control_map(controls['run_tests.py'], 'run_tests.py') == CONTROL_REASONS,
         'control inventory: run_tests.py')
    need(control_map(controls['check_controls.py'], 'check_controls.py') == EXTRA_REASONS,
         'control inventory: check_controls.py')
    return controls


def validate_outputs(data):
    outputs = read_json(data)
    need(type(outputs) is dict and set(outputs) == OUTPUT_NAMES, 'output registry coverage')
    need(all(type(value) is str and re.fullmatch('[0-9a-f]{64}', value)
             for value in outputs.values()), 'output registry digest')
    return outputs


def validate_python(files):
    for name, data in files.items():
        if not name.endswith('.py'):
            continue
        need('/' not in name, 'nested Python file')
        need(Path(name).stem not in sys.stdlib_module_names, 'standard-library module shadow')
        tree = ast.parse(data.decode(), filename=name)
        for node in ast.walk(tree):
            need(not isinstance(node, ast.Assert), 'assert in ' + name)
            need(not (isinstance(node, ast.Constant) and type(node.value) in (float, complex)),
                 'inexact literal in ' + name)
            roots = []
            if isinstance(node, ast.Import):
                roots = [entry.name.split('.')[0] for entry in node.names]
            elif isinstance(node, ast.ImportFrom):
                need(node.level == 0 and node.module, 'relative import in ' + name)
                roots = [node.module.split('.')[0]]
            need(all(root in sys.stdlib_module_names for root in roots),
                 'nonstandard import in ' + name)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                need(node.func.id not in {'float', 'complex', 'eval', 'exec', 'compile', '__import__'},
                     'inexact or dynamic call in ' + name)


def validate_directory(files):
    need(set(files) == EXPECTED_FILES, 'verification file coverage')
    manifest = {}
    for line in files['SHA256SUMS'].decode().splitlines():
        parts = line.split('  ', 1)
        need(len(parts) == 2 and re.fullmatch('[0-9a-f]{64}', parts[0]),
             'manifest syntax')
        sha, name = parts
        need(name not in manifest, 'duplicate manifest entry')
        manifest[name] = sha
    need(set(manifest) == set(files) - {'SHA256SUMS'}, 'manifest coverage')
    for name, expected in manifest.items():
        need(digest(files[name]) == expected, 'manifest mismatch: ' + name)
    for name, expected in CODE_HASHES.items():
        need(digest(files[name]) == expected, 'implementation source binding: ' + name)
    validate_python(files)
    for name, data in files.items():
        if name.endswith('.json'):
            read_json(data)
    outputs = validate_outputs(files['OUTPUT_HASHES.json'])
    controls = validate_controls(files['NEGATIVE_CONTROLS.json'])
    proofs = validate_bindings(files['SOURCE_BINDINGS.txt'])
    return outputs, controls, proofs


def remanifest(files):
    result = dict(files)
    result['SHA256SUMS'] = ''.join(digest(data) + '  ' + name + '\n'
        for name, data in sorted(result.items()) if name != 'SHA256SUMS').encode()
    return result


def integrity_controls(files):
    cases = []
    changed = dict(files)
    changed['generate.py'] += b'\n'
    cases.append((changed, 'manifest mismatch: generate.py'))
    cases.append((remanifest(changed), 'implementation source binding: generate.py'))
    missing = dict(files)
    del missing['verify.py']
    cases.append((missing, 'verification file coverage'))
    extra = dict(files)
    extra['unregistered.txt'] = b'extra\n'
    cases.append((extra, 'verification file coverage'))
    duplicate = dict(files)
    duplicate['SHA256SUMS'] += files['SHA256SUMS'].splitlines(keepends=True)[0]
    cases.append((duplicate, 'duplicate manifest entry'))
    incomplete = dict(files)
    incomplete['SHA256SUMS'] = b'\n'.join(files['SHA256SUMS'].splitlines()[1:]) + b'\n'
    cases.append((incomplete, 'manifest coverage'))
    weakened = dict(files)
    controls = read_json(weakened['NEGATIVE_CONTROLS.json'])
    controls['run_tests.py'].pop()
    weakened['NEGATIVE_CONTROLS.json'] = json.dumps(controls).encode()
    cases.append((remanifest(weakened), 'control inventory: run_tests.py'))
    unregistered = dict(files)
    outputs = read_json(unregistered['OUTPUT_HASHES.json'])
    del outputs['zero2.verify']
    unregistered['OUTPUT_HASHES.json'] = json.dumps(outputs).encode()
    cases.append((remanifest(unregistered), 'output registry coverage'))
    unbound = dict(files)
    unbound['SOURCE_BINDINGS.txt'] = files['SOURCE_BINDINGS.txt'].replace(
        SOURCE_HASHES['PROOF.md'].encode(), b'0' * 64)
    cases.append((remanifest(unbound), 'source proof hash'))
    for packet, expected in cases:
        try:
            validate_directory(packet)
        except SystemExit as error:
            need(str(error) == 'FAIL: ' + expected, 'integrity control wrong failure')
        else:
            need(False, 'integrity control accepted')
    return len(cases)


def execute(command, env, cwd, label, rejection=None):
    try:
        result = subprocess.run(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                capture_output=True, timeout=600)
    except subprocess.TimeoutExpired:
        raise SystemExit('FAIL: process timeout: ' + label)
    if rejection is not None:
        need(result.returncode == 1, 'rejection exit: ' + label)
        need(not result.stdout, 'rejection standard output: ' + label)
        need(result.stderr.startswith(('FAIL[' + rejection + ']:').encode()),
             'rejection reason: ' + label)
        return result.stderr
    need(result.returncode == 0, 'process exit: ' + label)
    need(not result.stderr, 'process standard error: ' + label)
    return result.stdout


def check_report(data):
    report = read_json(data)
    need(type(report) is dict and report.get('status') == 'PASS', 'harness report status')
    need(control_map(report.get('negative_controls'), 'report') == CONTROL_REASONS,
         'harness negative-control coverage')
    positives = report.get('positive_certificates')
    need(type(positives) is list and len(positives) == len(FIXTURES), 'positive count')
    need({entry['fixture'] for entry in positives} == set(FIXTURES), 'positive fixture coverage')
    need(report.get('inertia_unit_cases') == 9 and report.get('safeguarded_unit_cases') == 3,
         'arithmetic branch coverage')
    need(report.get('long_integer_roundtrip_decimal_digits') == 4401 and
         report.get('long_integer_fresh_loaders') == ['generate.py', 'verify.py'],
         'long-integer loader coverage')
    return {entry['fixture']: entry for entry in positives}


def scratch_base():
    root = HERE.parent
    directory = root / 'tmp' / 'verification'
    need(not (root / 'tmp').is_symlink() and not directory.is_symlink(), 'scratch symlink')
    directory.mkdir(parents=True, exist_ok=True)
    need(directory.resolve() == root / 'tmp' / 'verification', 'scratch location')
    return directory


def run_mode(mode, flags, seed, files):
    outputs = {}
    env = {'PATH': os.defpath, 'LC_ALL': 'C.UTF-8', 'PYTHONHASHSEED': seed}
    with tempfile.TemporaryDirectory(prefix=mode + '-', dir=scratch_base()) as temporary:
        work = Path(temporary)
        for name, data in files.items():
            target = work / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        command = [sys.executable, '-P', '-S', '-s', '-B'] + flags
        report_path = work / 'report.json'
        outputs['run_tests.stdout'] = execute(
            command + [str(work / 'run_tests.py'), '--report', str(report_path)],
            env, work, mode + ' harness')
        outputs['run_tests.report'] = report_path.read_bytes()
        positives = check_report(outputs['run_tests.report'])
        # The fixture harness uses -I for its children. Replay its corruptions
        # directly as well, so the selected hash seed reaches every verifier.
        bad_files = work / 'tmp' / ('optimized' if '-O' in flags else 'normal')
        for name, reason in CONTROL_REASONS.items():
            ip = bad_files / (name + '.input.json')
            cp = bad_files / (name + '.cert.json')
            outputs['negative.' + name] = execute(
                command + [str(work / 'verify.py'), str(ip), str(cp)],
                env, work, mode + ' negative ' + name, rejection=reason)
        direct = work / 'direct'
        direct.mkdir()
        for name in FIXTURES:
            ip = work / 'fixtures' / (name + '.json')
            cp = direct / (name + '.certificate.json')
            sp = direct / (name + '.stats.json')
            outputs[name + '.generate'] = execute(
                command + [str(work / 'generate.py'), str(ip), str(cp), '--stats', str(sp)],
                env, work, mode + ' generate ' + name)
            need(cp.read_bytes() == files['certificates/' + name + '.json'],
                 'certificate regeneration: ' + name)
            need(read_json(sp.read_bytes()) == positives[name]['construction'],
                 'construction statistics: ' + name)
            outputs[name + '.verify'] = execute(
                command + [str(work / 'verify.py'), str(ip), str(cp)],
                env, work, mode + ' verify ' + name)
            need(read_json(outputs[name + '.verify']) == positives[name]['verification'],
                 'verification report: ' + name)
        outputs['check_controls.stdout'] = execute(
            command + [str(work / 'check_controls.py'), '--work', str(work / 'additional')],
            env, work, mode + ' additional controls')
        additional = read_json(outputs['check_controls.stdout'])
        need(type(additional) is dict and set(additional) == {'status', 'negative_controls'}
             and additional['status'] == 'PASS', 'additional report status')
        need(control_map(additional['negative_controls'], 'additional') == EXTRA_REASONS,
             'additional control coverage')
        for name, data in files.items():
            path = work / name
            need(path.is_file() and not path.is_symlink() and path.read_bytes() == data,
                 'scratch source changed: ' + name)
    need(set(outputs) == OUTPUT_NAMES, 'observed output coverage')
    return outputs


def main():
    need(len(sys.argv) == 1, 'runner takes no arguments')
    files = inventory()
    registry, controls, proofs = validate_directory(files)
    integrity_count = integrity_controls(files)
    previous = None
    for mode, flags, seed in MODES:
        outputs = run_mode(mode, flags, seed, files)
        need({name: digest(data) for name, data in outputs.items()} == registry,
             'registered output mismatch: ' + mode)
        need(previous is None or outputs == previous, 'mode output mismatch: ' + mode)
        previous = outputs
    need(inventory() == files, 'verification files changed during execution')
    need(proof_inventory() == proofs, 'proof files changed during execution')
    print('PASS: 11 fixtures regenerated and verified in normal, optimized and hash-seed modes')
    print('PASS: 156 reason-specific negative-control runs; all 27 cases receive each selected mode')
    print('PASS: 9 inertia and 3 safeguarded cases per mode')
    print('PASS: 4401-digit fresh-loader checks; 2 proof bindings; immutable source inventory')
    print('PASS: ' + str(integrity_count) + ' runner integrity controls rejected')
    print('RESULT: PASS KE-02 finite-precision verification')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, SyntaxError, UnicodeError) as error:
        raise SystemExit('FAIL: verification input: ' + type(error).__name__)
