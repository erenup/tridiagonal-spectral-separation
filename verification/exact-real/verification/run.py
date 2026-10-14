#!/usr/bin/env python3
"""Check proof bindings, exact output hashes, and negative controls in three modes."""
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODES = [('normal', [], '1'), ('optimized', ['-O'], '1'), ('hash-seed', [], '8675309')]
MATH_INTEGER = {'ceil', 'comb', 'factorial', 'floor', 'gcd', 'isqrt', 'lcm', 'perm', 'prod', 'trunc'}
FORBIDDEN_CALLS = {'float', 'complex', 'eval', 'exec', 'compile', '__import__', 'getattr'}
FORBIDDEN_MODULES = {'cmath', 'decimal', 'statistics', 'importlib'}

FINITE_PRECISION_RUNNER_SHA256 = 'f8f63786f1f68cfad151b1054599cde7d9a4f62b38de611d6b4a79e8b8189ed3'
FINITE_PRECISION_OUTPUT_SHA256 = 'ab6977156c1f88059ac94b7c5bda64f2b28487ba019df823340b6408444cd873'

EXPECTED_CONTROLS = {'check_convex_selector.py': frozenset({'unguarded-radius', 'wrong-child', 'nonconvex-hinge', 'oracle-accuracy'}), 'check_inverse_tunneling.py': frozenset({'flattening-overlap', 'outside-leakage', 'wronskian-sign', 'projector-norm', 'weight-swap', 'gap-threshold', 'skipped-row-residual'}), 'check_primitives.py': frozenset({'graeffe-odd-sign', 'continuant-coupling-sign', 'negative-root-ratio', 'curvature-constant'}), 'check_recursive_primitives.py': frozenset({'graeffe-coefficient', 'characteristic-coefficient', 'missing-prefix-node', 'resonant-shift'})}
EXPECTED_SOURCE_HASHES = {'PROOF.md': '29cd49dddfaaf7104e7b025f07830f900f75633ed9b1aa0199b9ae8e22ee0d87', 'STATEMENT.md': '552028b08e633bdb618bc68171c60744262a1a4df77079ce0e00f39beb8cdb8b'}
EXPECTED_FILES = frozenset(EXPECTED_CONTROLS) | {'run.py', 'README.md', 'CHECKERS.txt', 'NEGATIVE_CONTROLS.json', 'SOURCE_BINDINGS.txt', 'SHA256SUMS'}


def need(ok, message):
    if not ok:
        raise SystemExit('FAIL: '+message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reject_number(value):
    raise SystemExit('FAIL: non-integer JSON number: '+value)


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def read_json(data):
    return json.loads(data, object_pairs_hook=unique_pairs,
                      parse_float=reject_number, parse_constant=reject_number)


def proof_inventory():
    root = HERE.parent/'proofs'
    need(root.is_dir() and not root.is_symlink(), 'invalid proof directory')
    paths = list(root.iterdir())
    need({p.name for p in paths} == {'PROOF.md', 'STATEMENT.md'}, 'proof coverage')
    need(all(p.is_file() and not p.is_symlink() for p in paths), 'invalid proof file')
    return {p.name: digest(p.read_bytes()) for p in paths}


def validate_bindings(data):
    registered = {}
    for line in data.decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        parts = line.split()
        need(len(parts) == 3 and all(re.fullmatch('[0-9a-f]{64}', s) for s in parts[:2]),
             'source binding syntax')
        source, document, name = parts
        need(EXPECTED_SOURCE_HASHES.get(name) == source, 'source proof hash mismatch')
        need(name not in registered, 'duplicate proof binding')
        registered[name] = document
    need(registered == proof_inventory(), 'proof binding mismatch')
    return registered


def validate_controls(data, registry):
    controls = read_json(data)
    need(type(controls) is dict and set(controls) == set(registry), 'negative-control coverage')
    for name, entries in controls.items():
        need(type(entries) is list and bool(entries), 'missing negative controls: '+name)
        seen = set()
        for entry in entries:
            need(type(entry) is dict and set(entry) == {'name', 'stderr'}, 'negative-control fields')
            label, error = entry['name'], entry['stderr']
            need(type(label) is str and re.fullmatch('[a-z][a-z0-9_-]*', label) is not None,
                 'negative-control name')
            need(label not in seen, 'duplicate negative control')
            seen.add(label)
            need(type(error) is str and bool(error.strip()) and error.endswith('\n'),
                 'negative-control expected error')
        need(seen == EXPECTED_CONTROLS[name], 'negative-control inventory: '+name)
    return controls


def validate_integer_fixture_random(tree, name):
    """Allow only the fixed integer fixture generator in the selector checker."""
    need(name == 'check_convex_selector.py', 'random import outside integer fixture checker')
    parents = {child: parent for parent in ast.walk(tree) for child in ast.iter_child_nodes(parent)}
    need(not any(isinstance(n, ast.ImportFrom) and n.module
                 and n.module.split('.')[0] == 'random' for n in ast.walk(tree)),
         'random fixture from-import')
    imports = [n for n in ast.walk(tree) if isinstance(n, ast.Import)
               and any(a.name.split('.')[0] == 'random' for a in n.names)]
    need(len(imports) == 1 and len(imports[0].names) == 1
         and imports[0].names[0].name == 'random' and imports[0].names[0].asname is None, 'integer fixture random import')
    constructors = []
    draws = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load) and node.id in {'random', 'rng'}:
            parent = parents.get(node)
            need(isinstance(parent, ast.Attribute) and parent.value is node,
                 'unrestricted random fixture reference')
            call = parents.get(parent)
            need(isinstance(call, ast.Call) and call.func is parent and not call.keywords,
                 'unrestricted random fixture call')
            if node.id == 'random':
                need(parent.attr == 'Random' and len(call.args) == 1
                     and isinstance(call.args[0], ast.Constant)
                     and type(call.args[0].value) is int and call.args[0].value == 20261012,
                     'integer fixture seed')
                constructors.append(call)
            else:
                need(parent.attr == 'randrange', 'non-integer random fixture method')
                draws.append(call)
    need(len(constructors) == 1 and len(draws) == 2, 'integer fixture generator coverage')
    writes = [n for n in ast.walk(tree) if isinstance(n, ast.Name)
              and isinstance(n.ctx, ast.Store) and n.id == 'rng']
    need(len(writes) == 1 and isinstance(parents.get(writes[0]), ast.Assign)
         and parents[writes[0]].value is constructors[0], 'integer fixture generator assignment')
    allowed = {ast.dump(ast.parse(expr, mode='eval').body, include_attributes=False)
               for expr in ('rng.randrange(-20,121)', 'rng.randrange(1,10)')}
    need({ast.dump(call, include_attributes=False) for call in draws} == allowed,
         'integer fixture draw ranges')


def inventory():
    files = {}
    for path in HERE.rglob('*'):
        need(not path.is_symlink(), 'symbolic link: '+str(path.relative_to(HERE)))
        if path.is_file():
            name = path.relative_to(HERE).as_posix()
            need('__pycache__' not in path.parts and not name.endswith('.pyc'), 'cache file: '+name)
            need(path.stat().st_size <= 4500000, 'file size: '+name)
            files[name] = path.read_bytes()
    return files


def validate_directory(files=None):
    if files is None:
        files = inventory()
    need(set(files) == EXPECTED_FILES, 'verification file coverage')
    need('SHA256SUMS' in files and 'CHECKERS.txt' in files, 'missing manifest or registry')
    sums = {}
    for line in files['SHA256SUMS'].decode().splitlines():
        parts = line.split('  ', 1)
        need(len(parts) == 2 and re.fullmatch('[0-9a-f]{64}', parts[0]) is not None, 'manifest syntax')
        sha, name = parts
        need(name not in sums, 'duplicate manifest entry')
        sums[name] = sha
    need(set(sums) == set(files)-{'SHA256SUMS'}, 'manifest coverage')
    for name, sha in sums.items():
        need(digest(files[name]) == sha, 'manifest mismatch: '+name)
    registry = {}
    for line in files['CHECKERS.txt'].decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        parts = line.split()
        need(len(parts) == 2 and re.fullmatch(r'check_[a-z0-9_]+\.py', parts[0]) is not None
             and re.fullmatch('[0-9a-f]{64}', parts[1]) is not None, 'registry syntax')
        name, sha = parts
        need(name not in registry, 'duplicate checker')
        registry[name] = sha
    need(set(registry) == set(EXPECTED_CONTROLS), 'checker inventory')
    python_files = {name for name in files if name.endswith('.py')}
    need(all('/' not in name for name in python_files), 'Python file below top level')
    need(bool(registry) and set(registry) == {n for n in python_files if n.startswith('check_')}, 'registry coverage')
    modules = {Path(n).stem for n in python_files}
    need(not (modules & sys.stdlib_module_names), 'standard-library module shadow')
    used = set()
    for name in sorted(python_files):
        tree = ast.parse(files[name].decode(), filename=name)
        for node in ast.walk(tree):
            need(not isinstance(node, ast.Assert), 'assert in '+name)
            if isinstance(node, ast.ImportFrom):
                need(node.level == 0 and node.module, 'relative import in '+name)
                roots = [node.module.split('.')[0]]
                if node.module == 'math':
                    need(all(n.name in MATH_INTEGER for n in node.names), 'non-integer math import')
            elif isinstance(node, ast.Import):
                roots = [n.name.split('.')[0] for n in node.names]
            else:
                roots = []
            for root in roots:
                need(root in sys.stdlib_module_names | modules, 'nonstandard import in '+name)
                need(root not in FORBIDDEN_MODULES, 'inexact or dynamic module in '+name)
                if root == 'random':
                    validate_integer_fixture_random(tree, name)
                if name != 'run.py':
                    need(root not in {'subprocess', 'multiprocessing', 'concurrent'}, 'checker process import')
                    used.add(root)
            need(not (isinstance(node, ast.Constant) and type(node.value).__name__ in {'float', 'complex'}), 'inexact literal in '+name)
            if isinstance(node, ast.Call):
                if isinstance(node.func, ast.Name):
                    need(node.func.id not in FORBIDDEN_CALLS, 'inexact or dynamic call in '+name)
                if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id == 'math':
                    need(node.func.attr in MATH_INTEGER, 'non-integer math call')
    helpers = modules-{'run'}-{Path(n).stem for n in registry}
    need(helpers <= used, 'unused arithmetic module')
    for name, data in files.items():
        if name.endswith('.json'):
            read_json(data)
    proofs = validate_bindings(files['SOURCE_BINDINGS.txt'])
    controls = validate_controls(files['NEGATIVE_CONTROLS.json'], registry)
    return registry, controls, proofs, {name: digest(data) for name, data in files.items()}


def execute(command, env, label):
    try:
        return subprocess.run(command, cwd=HERE, env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, timeout=600)
    except subprocess.TimeoutExpired:
        raise SystemExit('FAIL: checker timeout: '+label)


def integrity_controls(files):
    """Reject altered content, incomplete coverage and weakened controls in memory."""
    cases = []
    changed = dict(files)
    changed['check_primitives.py'] += b'\n# altered bytes\n'
    cases.append((changed, 'manifest mismatch: check_primitives.py'))
    missing = dict(files)
    del missing['check_primitives.py']
    cases.append((missing, 'verification file coverage'))
    duplicate = dict(files)
    duplicate['SHA256SUMS'] += files['SHA256SUMS'].splitlines(keepends=True)[0]
    cases.append((duplicate, 'duplicate manifest entry'))
    extra = dict(files)
    extra['unregistered.txt'] = b'extra\n'
    cases.append((extra, 'verification file coverage'))
    weakened = dict(files)
    controls = read_json(weakened['NEGATIVE_CONTROLS.json'])
    controls['check_primitives.py'] = controls['check_primitives.py'][1:]
    weakened['NEGATIVE_CONTROLS.json'] = (json.dumps(controls, indent=2, sort_keys=True)+'\n').encode()
    weakened['SHA256SUMS'] = ''.join(digest(data)+'  '+name+'\n'
        for name, data in sorted(weakened.items()) if name != 'SHA256SUMS').encode()
    cases.append((weakened, 'negative-control inventory: check_primitives.py'))
    inexact_import = dict(files)
    inexact_import['check_convex_selector.py'] = inexact_import['check_convex_selector.py'].replace(
        b'import random\n', b'import random\nfrom random import uniform\n')
    inexact_import['SHA256SUMS'] = ''.join(digest(data)+'  '+name+'\n'
        for name, data in sorted(inexact_import.items()) if name != 'SHA256SUMS').encode()
    cases.append((inexact_import, 'random fixture from-import'))
    for packet, expected in cases:
        try:
            validate_directory(packet)
        except SystemExit as error:
            need(str(error) == 'FAIL: '+expected, 'integrity control wrong failure')
        else:
            need(False, 'integrity control accepted')
    return len(cases)


FINITE_PRECISION_MANIFEST_SHA256 = 'f6de8965cbd728acc7d829f8d34b7dace69177b3aa3ee817767e67ca0471b829'


def authenticate_child_manifest(verification, expected, label):
    manifest = verification / 'SHA256SUMS'
    need(manifest.is_file() and not manifest.is_symlink(), label+' missing regular manifest')
    need(digest(manifest.read_bytes()) == expected, label+' manifest binding mismatch')


def run_finite_precision():
    directory = HERE.parents[1]/'finite-precision'
    need(directory.is_dir() and not directory.is_symlink(), 'invalid finite-precision directory')
    verification = directory/'verification'
    need(verification.is_dir() and not verification.is_symlink(), 'invalid finite-precision verification directory')
    runner = verification/'run.py'
    need(runner.is_file() and not runner.is_symlink(), 'missing finite-precision runner')
    need(digest(runner.read_bytes()) == FINITE_PRECISION_RUNNER_SHA256,
         'finite-precision runner source mismatch')
    authenticate_child_manifest(verification, FINITE_PRECISION_MANIFEST_SHA256, 'finite-precision')
    flags = ['-O'] if sys.flags.optimize else []
    try:
        result = subprocess.run([sys.executable, '-S', '-s', '-B']+flags+[str(runner)],
                                cwd=HERE, stdin=subprocess.DEVNULL, capture_output=True, timeout=600,
                                env={'PATH': os.defpath, 'LC_ALL': 'C.UTF-8', 'PYTHONHASHSEED': '1'})
    except subprocess.TimeoutExpired:
        raise SystemExit('FAIL: finite-precision suite timed out')
    need(result.returncode == 0 and not result.stderr, 'finite-precision suite failed')
    need(digest(result.stdout) == FINITE_PRECISION_OUTPUT_SHA256,
         'finite-precision suite output mismatch')
    need(runner.is_file() and not runner.is_symlink()
         and digest(runner.read_bytes()) == FINITE_PRECISION_RUNNER_SHA256,
         'finite-precision runner changed during execution')
    authenticate_child_manifest(verification, FINITE_PRECISION_MANIFEST_SHA256, 'finite-precision')
    print(result.stdout.decode(), end='')


def main():
    registry, controls, proofs, before = validate_directory()
    integrity_count = integrity_controls(inventory())
    negative_runs = 0
    for name, expected in sorted(registry.items()):
        previous = None
        for mode, flags, seed in MODES:
            command = [sys.executable, '-S', '-s', '-B']+flags+[str(HERE/name)]
            env = {'PATH': os.defpath, 'LC_ALL': 'C.UTF-8', 'PYTHONHASHSEED': seed}
            result = execute(command, env, name+' '+mode)
            need(result.returncode == 0, 'checker exit status: '+name+' '+mode)
            need(not result.stderr, 'checker standard error: '+name+' '+mode)
            need(digest(result.stdout) == expected, 'output hash mismatch: '+name+' '+mode)
            need(previous is None or previous == result.stdout, 'mode mismatch: '+name)
            previous = result.stdout
            for control in controls[name]:
                label = name+' '+mode+' '+control['name']
                result = execute(command+['--negative-control', control['name']], env, label)
                need(result.returncode == 1, 'negative-control exit status: '+label)
                need(not result.stdout, 'negative-control standard output: '+label)
                need(result.stderr == control['stderr'].encode(), 'negative-control error: '+label)
                negative_runs += 1
        print('PASS: '+name+' (normal, optimized, hash-seed)')
    after = {name: digest(data) for name, data in inventory().items()}
    need(after == before, 'verification files changed during execution')
    need(proof_inventory() == proofs, 'proof files changed during execution')
    print('PASS: '+str(negative_runs)+' negative-control runs; 2 proof bindings')
    print('PASS: '+str(integrity_count)+' integrity controls rejected')
    run_finite_precision()
    print('RESULT: PASS KE-02 verification')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, SyntaxError, UnicodeError) as error:
        raise SystemExit('FAIL: verification input: '+type(error).__name__)
