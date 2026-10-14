#!/usr/bin/env python3
"""Fail-closed clean compiler build of the fixed KE-02 scalar/algebra core.

Dependencies use the existing pinned official cache, read only. Project objects
are built into a newly created directory; no development objects are imported.
The finite rational screen is supplementary, never a universal proof premise.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
LEAN_SHA256 = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
SOURCE_MANIFEST_SHA256 = '2fd95aaac0b5f7a568725eab497709f2ff23547b63154be3b5d2cda2ac9dc884'
HELPER_HASHES = {'audit/check_exact.py': '7e36f83f4ee5433c9003e077904c438fbd8db6ecde2ebe88152e5c4c62d2616e', 'audit/test_exact.py': '7ef0325b6a5e82480b82d37739bd8b8eebf97b3c3b3ee0e18fde790213e32681', 'audit/test_verify.py': 'd3c4d5b02aca6d2a8afb7bc5248067ca4b8c549e9faf9c23b5725c2d7e5f590e'}
FIXED_HASHES = {
    'KE02/SelectorDefinitions.lean': 'dea05f22aab2e8f386a270f3686c5c6ea37cb7de049dde75815dde4928fa72ce',
    'KE02/SelectorStatement.lean': '881fa9dbde96d85a4109a7a5988a9a60b82127d720edce15d30cb868cc6e1ce9',
    'KE02/GraeffeDefinitions.lean': '20ed18c09666c56902c70779c25e9b57864e1f16fd8d0810911382aeaf26a910',
    'KE02/GraeffeStatement.lean': '13854db5232f75331ee54380c7bc782db46226d4696eb6085c9d14f3c93eb99e',
    'KE02/CoefficientDefinitions.lean': 'c57a83be0d91beb4d85ac88db79e2a15298b7cb8da69e8fd8760f11c6fc9e346',
    'KE02/CoefficientStatement.lean': '1bc613201f9fd907aaf5f8e5430be1d0b7ef9a3231f983b78c0f0674b262777e',
    'KE02/Statement.lean': 'b3d0d608c158b42afb32977c64a1001bfde5356a7d82e2e797956b35bab5a9e7',
    'FEASIBILITY_SCOPE.md': '204fb57be41dc2f63ed0a0cdaf39f6b3f9a2a175d7305322391ad1772bdaa51c',
}
CONFIG_FILES = frozenset({'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                          'audit/statement-hashes.json', 'README.md', 'FEASIBILITY_SCOPE.md', '.gitignore', 'verify.py'})
HELPERS = frozenset({'audit/check_exact.py', 'audit/test_exact.py', 'audit/test_verify.py'})
THEOREM = 'KE02.coreCertificate'
EXPECTED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
AXIOMS_SOURCE = ('import KE02\n\n'
    'example : KE02.CoreCertificate := KE02.coreCertificate\n\n'
    '#print axioms KE02.coreCertificate\n')
AXIOMS_OUTPUT = re.compile(r"\s*'KE02\.coreCertificate' depends on axioms: \[([^\[\]\r\n]*)\]\s*\Z")
MODULE_PATH = re.compile(r'KE02(?:/[A-Za-z][A-Za-z0-9_]*)*\.lean\Z')
SHA256 = re.compile(r'[0-9a-f]{64}\Z')
# Scan comments/strings too. This deliberately rejects local metaprogramming,
# runtime/kernel shortcuts and arbitrary compiler directives in proof sources.
FORBIDDEN = re.compile(r'\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|native_eval|'
    r'ofReduceBool|ofReduceNat|implemented_by|extern|skipKernelTC|debug|'
    r'initialize|builtin_initialize|elab|elab_rules|macro|macro_rules|syntax|'
    r'run_tac|run_elab|eval_expr|Lean\.Environment\.add|setReducibilityStatus)\b')
SAFE_OPTIONS = frozenset({'maxRecDepth', 'maxHeartbeats', 'linter.unusedTactic',
                          'linter.unusedSimpArgs', 'linter.unnecessarySeqFocus',
                          'linter.unusedVariables'})
BASE_ENV = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
            'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': '/dev/null',
            'GIT_CONFIG_SYSTEM': '/dev/null', 'GIT_OPTIONAL_LOCKS': '0',
            'OMP_NUM_THREADS': '1', 'OPENBLAS_NUM_THREADS': '1', 'MKL_NUM_THREADS': '1'}
GIT = ['/usr/bin/git', '--no-optional-locks', '-c', 'core.fsmonitor=false']


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def read_regular(root, name):
    path = root / name
    require(path.is_file(), f'Missing file: {name}')
    for item in [path, *path.parents]:
        require(not item.is_symlink(), f'Linked project file: {name}')
        if item == root:
            break
    return path.read_bytes()


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, f'Duplicate JSON field: {key}')
        out[key] = value
    return out


def load_binding(raw):
    try:
        value = json.loads(raw.decode('utf-8'), object_pairs_hook=unique_object)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise AuditError('Malformed source manifest') from error
    require(isinstance(value, dict) and set(value) == {'schema', 'sources', 'configuration'},
            'Invalid source manifest fields')
    require(type(value['schema']) is int and value['schema'] == 1, 'Invalid manifest schema')
    for section in ['sources', 'configuration']:
        require(isinstance(value[section], dict) and value[section], 'Empty binding section')
        for name, digest in value[section].items():
            require(isinstance(name, str) and isinstance(digest, str) and SHA256.fullmatch(digest),
                    'Invalid source binding')
            if section == 'sources':
                require(MODULE_PATH.fullmatch(name) is not None, 'Invalid bound module path')
    require(set(value['configuration']) == CONFIG_FILES, 'Configuration inventory differs')
    require('KE02.lean' in value['sources'], 'Missing aggregate theorem binding')
    return value


def reject_forbidden(source, name):
    match = FORBIDDEN.search(source)
    require(match is None, f'Disallowed proof token in {name}: {match.group(0) if match else ""}')
    require('#' not in source, f'Disallowed compiler directive in {name}')
    options = re.findall(r'\bset_option\s+([^\s]+)', source)
    require(all(option in SAFE_OPTIONS for option in options), f'Disallowed compiler option in {name}')


def source_paths(root):
    require(root.is_dir() and not root.is_symlink(), 'Invalid project directory')
    found = []
    def walk_error(error):
        raise AuditError(f'Cannot enumerate sources: {error}')
    for directory, dirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        current = Path(directory)
        if current == root:
            dirs[:] = [d for d in dirs if d not in {'.lake', '.git'}]
            files = [f for f in files if f != '.git']
        for name in dirs + files:
            require(not (current / name).is_symlink(),
                    f'Project symlink is not allowed: {(current / name).relative_to(root)}')
        found.extend(current / name for name in files if name.endswith('.lean'))
    return sorted(found)


def check_sources(root):
    raw = read_regular(root, 'audit/source-hashes.json')
    require(sha(raw) == SOURCE_MANIFEST_SHA256, 'Source manifest digest differs')
    binding = load_binding(raw)
    snapshot = {'audit/source-hashes.json': raw}
    actual = {p.relative_to(root).as_posix() for p in source_paths(root)}
    require(actual == set(binding['sources']) | {'audit/Axioms.lean'}, 'Lean source inventory differs')
    for name, digest in {**binding['sources'], **binding['configuration']}.items():
        data = read_regular(root, name)
        require(sha(data) == digest, f'Bound file changed: {name}')
        if name.endswith('.lean'):
            try:
                reject_forbidden(data.decode('utf-8'), name)
            except UnicodeError as error:
                raise AuditError(f'Invalid source encoding: {name}') from error
        snapshot[name] = data
    for name, expected in FIXED_HASHES.items():
        require(name in snapshot and sha(snapshot[name]) == expected, f'Fixed statement changed: {name}')
    probe = read_regular(root, 'audit/Axioms.lean')
    require(probe == AXIOMS_SOURCE.encode(), 'Axiom probe changed')
    snapshot['audit/Axioms.lean'] = probe
    return snapshot


def check_helpers(root):
    require(set(HELPER_HASHES) == HELPERS, 'Audit helper hashes not frozen')
    actual = {p.relative_to(root).as_posix() for p in (root / 'audit').rglob('*.py')}
    require(actual == HELPERS | {'audit/verify.py'}, 'Audit helper inventory differs')
    snapshot = {}
    for name in sorted(actual):
        snapshot[name] = read_regular(root, name)
        if name in HELPER_HASHES:
            require(sha(snapshot[name]) == HELPER_HASHES[name], f'Audit helper changed: {name}')
    return snapshot


def module_order(snapshot):
    sources = {name[:-5].replace('/', '.'): data.decode('utf-8') for name, data in snapshot.items()
               if MODULE_PATH.fullmatch(name)}
    visiting, visited, ordered = set(), set(), []
    def visit(module):
        require(module in sources, f'Missing local import: {module}')
        require(module not in visiting, f'Import cycle: {module}')
        if module in visited:
            return
        visiting.add(module)
        for line in sources[module].splitlines():
            match = re.match(r'\s*(?:(?:public|private)\s+)?import\s+(.+)', line)
            if match:
                for dep in match.group(1).split('--', 1)[0].split():
                    if dep == 'KE02' or dep.startswith('KE02.'):
                        visit(dep)
        visiting.remove(module)
        visited.add(module)
        ordered.append(module)
    for module in sorted(sources):
        visit(module)
    return ordered


def parse_axioms(stdout, stderr=''):
    require(not stderr, 'Unexpected axiom standard error')
    match = AXIOMS_OUTPUT.fullmatch(stdout)
    require(match is not None, 'Malformed or additional axiom output')
    names = [name.strip() for name in match.group(1).split(',')]
    require(len(names) == 3 and set(names) == EXPECTED_AXIOMS, f'Unexpected axioms: {names}')
    return sorted(names)


PYTHON_CHILDREN = {'audit/check_exact.py': ['7e36f83f4ee5433c9003e077904c438fbd8db6ecde2ebe88152e5c4c62d2616e', '28bb099d9189d9887cc00651cbe5e3350da239dec2d7e633bb67799975da2379', 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855']}


def run_python_checked(command, root, *args, **kwargs):
    """Authenticate the complete helper program and its expected diagnostics."""
    root = Path(root)
    names = [name for name in PYTHON_CHILDREN
             if name in command or str(root / name) in command]
    require(len(names) == 1, 'Unregistered Python audit child')
    name = names[0]
    path = root / name
    source_hash, stdout_hash, stderr_hash = PYTHON_CHILDREN[name]
    def source():
        require(all(not (root / Path(*Path(name).parts[:i])).is_symlink()
                    for i in range(1, len(Path(name).parts) + 1)),
                'Linked Python audit child: ' + name)
        require(path.is_file(), 'Missing Python audit child: ' + name)
        data = path.read_bytes()
        require(hashlib.sha256(data).hexdigest() == source_hash,
                'Python audit child source mismatch: ' + name)
        return data
    before = source()
    result = run_checked(command, root, *args, **kwargs)
    require(result.returncode == 0, 'Python audit child failed: ' + name)
    stdout, stderr = result.stdout, result.stderr
    if name == 'audit/test_verify.py':
        # unittest's duration is diagnostic; all remaining bytes are bound.
        stderr = re.sub(r'Ran (\d+) tests in [0-9.]+s',
                        r'Ran \1 tests in <time>s', stderr)
    require(hashlib.sha256(stdout.encode('utf-8')).hexdigest() == stdout_hash
            and hashlib.sha256(stderr.encode('utf-8')).hexdigest() == stderr_hash,
            'Python audit child output mismatch: ' + name)
    require(source() == before, 'Python audit child changed during execution: ' + name)
    return result


def run_checked(argv, cwd, env=None, log=None, timeout=1200):
    try:
        result = subprocess.run(argv, cwd=cwd, env=BASE_ENV if env is None else env,
                                capture_output=True, text=True,
                                encoding='utf-8', timeout=timeout, check=False)
    except (OSError, UnicodeError, subprocess.TimeoutExpired) as error:
        raise AuditError(f'Process could not complete: {argv[0]}: {error}') from error
    if log is not None:
        Path(str(log) + '.stdout').write_text(result.stdout)
        Path(str(log) + '.stderr').write_text(result.stderr)
    require(result.returncode == 0, f'Process failed with status {result.returncode}: {argv[0]}')
    return result


def resolve_compiler(root):
    """Resolve the project's toolchain through Lake without inheriting overrides."""
    executable = shutil.which('lake')
    require(executable is not None, 'Lake executable is unavailable on PATH')
    lake = Path(executable).absolute()
    env = dict(BASE_ENV)
    env['PATH'] = str(lake.parent) + os.pathsep + os.defpath
    for name in ['HOME', 'ELAN_HOME']:
        if name in os.environ:
            env[name] = os.environ[name]
    result = run_checked([str(lake), '--no-build', 'env', 'lean', '--print-prefix'],
                         root, env)
    require(not result.stderr, 'Unexpected Lake resolver standard error')
    lines = result.stdout.splitlines()
    require(len(lines) == 1 and lines[0] and lines[0] == lines[0].strip(),
            'Malformed Lake compiler prefix')
    prefix = Path(lines[0])
    require(prefix.is_absolute(), 'Lake compiler prefix is not absolute')
    lean = prefix / 'bin/lean'
    require(lean.is_file(), 'Resolved Lean compiler is missing')
    lean = lean.resolve(strict=True)
    require(file_sha(lean) == LEAN_SHA256, 'Compiler digest differs')
    return lean


def dependency_snapshot(root, lean):
    require(file_sha(lean) == LEAN_SHA256, 'Compiler digest differs')
    toolchain_lib = lean.parent.parent / 'lib'
    runtime = {}
    for path in sorted(toolchain_lib.rglob('*')):
        require(not path.is_symlink() or path.is_file(),
                f'Unsupported toolchain directory or dangling link: {path}')
        if path.is_file():
            require(path.resolve().is_relative_to(toolchain_lib.resolve()),
                    f'Toolchain artifact resolves outside installed toolchain: {path}')
            runtime[path.relative_to(toolchain_lib).as_posix()] = {
                'sha256': file_sha(path),
                'symlink': str(path.readlink()) if path.is_symlink() else None}
    version = run_checked([str(lean), '--version'], root).stdout.strip()
    require('4.34.0-rc2' in version and '6a10ac8c22beadecabdbb0919c2b50214762f91d' in version,
            'Compiler version differs')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages, libraries = {}, []
    for entry in manifest['packages']:
        dep = (root / '.lake/packages' / entry['name']).resolve(strict=True)
        revision = run_checked([*GIT, 'rev-parse', 'HEAD'], dep).stdout.strip()
        require(revision == entry['rev'], f'Dependency revision differs: {entry["name"]}')
        require(not run_checked([*GIT, 'status', '--porcelain', '--untracked-files=no'], dep).stdout,
                f'Dependency tracked sources dirty: {entry["name"]}')
        lib = dep / '.lake/build/lib/lean'
        hashes = {}
        if lib.is_dir():
            libraries.append(lib)
            for path in sorted(lib.rglob('*')):
                require(not path.is_symlink(), f'Linked cache artifact: {path}')
                if path.is_file():
                    relative = path.relative_to(lib).as_posix()
                    require(not relative.startswith(('KE02/', 'KE02.')), 'Local theorem shadowed in cache')
                    hashes[relative] = file_sha(path)
        packages[entry['name']] = {'revision': revision, 'path': str(dep), 'files': hashes}
    return {'compiler': LEAN_SHA256, 'version': version, 'toolchain_libraries': runtime,
            'packages': packages}, libraries


def prepare_output(path, root, lean):
    path = Path(path).absolute()
    require(not path.exists() and not path.is_symlink(), 'Build output already exists')
    require(not any(p.is_symlink() for p in path.parents), 'Build output parent is linked')
    path = path.resolve(strict=False)
    require(not path.is_relative_to(root.resolve() / '.lake'), 'Build output overlaps development objects')
    require(not path.is_relative_to(lean.parent.parent.resolve()), 'Build output overlaps toolchain')
    cache = root / '.lake/packages'
    if cache.is_dir():
        for dependency in cache.iterdir():
            require(not path.is_relative_to(dependency.resolve()), 'Build output overlaps dependency cache')
    require(not path.exists(), 'Build output already exists')
    path.mkdir(parents=True)
    objects = path / 'objects'
    objects.mkdir()
    return path, objects


def verify(output, root=ROOT):
    root = Path(root).absolute()
    started = time.monotonic()
    helpers = check_helpers(root)
    sources = check_sources(root)
    lean = resolve_compiler(root)
    output, objects = prepare_output(output, root, lean)
    print('Snapshotting pinned dependency cache (read only).', flush=True)
    dependencies, libraries = dependency_snapshot(root, lean)
    (output / 'DEPENDENCIES.json').write_text(json.dumps(dependencies, indent=2) + '\n')
    env = {'PATH': str(lean.parent) + os.pathsep + os.defpath,
           'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
           'LEAN_PATH': os.pathsep.join(str(p) for p in [objects, *libraries]),
           'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'OPENBLAS_NUM_THREADS': '1',
           'MKL_NUM_THREADS': '1'}
    runs = []
    for module in module_order(sources):
        source = root / (module.replace('.', '/') + '.lean')
        target = objects / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        argv = [str(lean), '-j1', '-M12288', '-o', str(target), str(source)]
        before = time.monotonic()
        result = run_checked(argv, root, env, output / module)
        require(target.is_file() and target.stat().st_size > 0, f'Missing compiled module: {module}')
        require(not result.stderr, f'Compiler standard error: {module}')
        # Successful Lean warnings are retained, never confused with axiom output.
        runs.append({'module': module, 'argv': argv, 'seconds': time.monotonic() - before,
                     'object_sha256': file_sha(target), 'returncode': result.returncode})
        print(f'PASS compiled {module}', flush=True)
    probe = run_checked([str(lean), '-j1', '-M12288', str(root / 'audit/Axioms.lean')],
                        root, env, output / 'AXIOMS')
    axioms = parse_axioms(probe.stdout, probe.stderr)
    print(probe.stdout, end='', flush=True)
    screen = run_python_checked([sys.executable, '-I', '-B', str(root / 'audit/check_exact.py')],
                         root, log=output / 'EXACT_SCREEN')
    require(not screen.stderr, 'Unexpected exact screen standard error')
    require(json.loads(screen.stdout)['status'] == 'PASS', 'Exact screen did not pass')
    require(check_sources(root) == sources, 'Sources changed during build')
    require(check_helpers(root) == helpers, 'Audit implementation changed during build')
    print('Checking dependency cache remained byte-identical.', flush=True)
    require(resolve_compiler(root) == lean, 'Resolved compiler changed during build')
    after, after_libraries = dependency_snapshot(root, lean)
    require(after == dependencies and after_libraries == libraries, 'Dependencies changed during build')
    receipt = {'status': 'PASS', 'build_mode': 'clean', 'theorem': THEOREM, 'axioms': axioms,
               'project_objects_initially_empty': True, 'dependencies_byte_identical': True,
               'source_manifest_sha256': SOURCE_MANIFEST_SHA256,
               'verifier_sha256': sha(helpers['audit/verify.py']),
               'dependency_manifest_sha256': file_sha(output / 'DEPENDENCIES.json'),
               'modules': runs, 'seconds': time.monotonic() - started}
    (output / 'BUILD_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'PASS: {len(runs)} modules freshly compiled; exact standard axiom set.', flush=True)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default=Path('.audit-build'), type=Path,
                        help='new, nonexistent build directory (default: .audit-build)')
    args = parser.parse_args()
    try:
        verify(args.output)
    except (AuditError, OSError, ValueError, KeyError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
