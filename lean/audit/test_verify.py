#!/usr/bin/env python3
"""Behavioral controls for the clean-build verifier; no Lean or cache build is run.

Synthetic bindings isolate each rejection. The fixed definition/statement hashes
are never patched: every positive fixture copies their actual frozen bytes.
Compiler/dependency effects are simulated only when testing the orchestration.
"""
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
VERIFY_PATH = ROOT / 'audit/verify.py'
v = types.ModuleType('ke02_verifier_under_test')
v.__file__ = str(VERIFY_PATH)
exec(compile(VERIFY_PATH.read_bytes(), str(VERIFY_PATH), 'exec'), v.__dict__)
GOOD_AXIOMS = "'KE02.coreCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]\n"


class VerifierControls(unittest.TestCase):
    def setUp(self):
        scratch = ROOT / '.audit-tests'
        scratch.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix='fixture-', dir=scratch)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'project'
        self.root.mkdir()
        self.lean = Path(self.temp.name) / 'toolchain/bin/lean'
        self.fixed = dict(v.FIXED_HASHES)
        for name in set(v.FIXED_HASHES) | set(v.CONFIG_FILES):
            self.write(name, (ROOT / name).read_bytes())
        self.write('KE02.lean', 'import KE02.Statement\nimport KE02.Fixture\n')
        self.write('KE02/Fixture.lean', 'namespace KE02\ntheorem fixture : True := by trivial\nend KE02\n')
        self.write('audit/Axioms.lean', v.AXIOMS_SOURCE)
        for name in v.HELPERS:
            self.write(name, '# controlled fixture helper\n')
        self.write('audit/verify.py', VERIFY_PATH.read_bytes())
        self.helper_hashes = {name: v.sha((self.root / name).read_bytes()) for name in v.HELPERS}
        self.helper_patch = patch.object(v, 'HELPER_HASHES', self.helper_hashes)
        self.helper_patch.start()
        self.addCleanup(self.helper_patch.stop)
        # Bind the deliberately synthetic screen and its complete successful output.
        child_binding = {'audit/check_exact.py': [self.helper_hashes['audit/check_exact.py'],
                         v.sha(b'{"status": "PASS"}\n'), v.sha(b'')]}
        child_patch = patch.object(v, 'PYTHON_CHILDREN', child_binding)
        child_patch.start()
        self.addCleanup(child_patch.stop)
        self.manifest_patch = patch.object(v, 'SOURCE_MANIFEST_SHA256', '')
        self.manifest_patch.start()
        self.addCleanup(self.manifest_patch.stop)
        self.rebind()
        # A failure below cannot be blamed on an invalid initial fixture.
        v.check_sources(self.root)
        v.check_helpers(self.root)

    def tearDown(self):
        self.assertEqual(v.FIXED_HASHES, self.fixed, 'Fixed hashes must never be patched')

    def write(self, name, data):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data.encode() if isinstance(data, str) else data)

    def rebind(self):
        sources = {p.relative_to(self.root).as_posix(): v.sha(p.read_bytes())
                   for p in self.root.rglob('*.lean')
                   if p.relative_to(self.root).as_posix() != 'audit/Axioms.lean'}
        config = {name: v.sha((self.root / name).read_bytes()) for name in v.CONFIG_FILES}
        self.binding = {'schema': 1, 'sources': sources, 'configuration': config}
        self.set_manifest(json.dumps(self.binding, sort_keys=True).encode())

    def set_manifest(self, data):
        self.write('audit/source-hashes.json', data)
        v.SOURCE_MANIFEST_SHA256 = v.sha(data)

    def rejected(self, function, message, *args):
        with self.assertRaisesRegex(v.AuditError, message):
            function(*args)

    def test_positive_fixture_and_import_order(self):
        snapshot = v.check_sources(self.root)
        order = v.module_order(snapshot)
        self.assertLess(order.index('KE02.Fixture'), order.index('KE02'))
        self.assertLess(order.index('KE02.GraeffeDefinitions'), order.index('KE02.GraeffeStatement'))
        self.assertEqual(set(snapshot), set(self.binding['sources']) | set(v.CONFIG_FILES) |
                         {'audit/Axioms.lean', 'audit/source-hashes.json'})

    def test_manifest_digest_tamper(self):
        with (self.root / 'audit/source-hashes.json').open('ab') as stream:
            stream.write(b' ')
        self.rejected(v.check_sources, 'manifest digest', self.root)

    def test_duplicate_manifest_field(self):
        raw = json.dumps(self.binding).encode().replace(b'"schema": 1', b'"schema": 1, "schema": 1')
        self.set_manifest(raw)
        self.rejected(v.check_sources, 'Duplicate JSON field', self.root)

    def test_malformed_manifest_variants(self):
        variants = [b'not json', b'\xff', b'[]']
        for raw in variants:
            with self.subTest(raw=repr(raw)):
                self.set_manifest(raw)
                self.rejected(v.check_sources, 'Malformed|Invalid', self.root)

    def test_invalid_binding_inventory_and_paths(self):
        variants = []
        for invalid in ['../Escape.lean', '/KE02.lean', 'Other.lean', 'KE02/../Escape.lean']:
            b = copy.deepcopy(self.binding)
            b['sources'][invalid] = '0' * 64
            variants.append(b)
        for value in [True, 2, '1']:
            b = copy.deepcopy(self.binding)
            b['schema'] = value
            variants.append(b)
        b = copy.deepcopy(self.binding)
        b['configuration'].pop('lean-toolchain')
        variants.append(b)
        b = copy.deepcopy(self.binding)
        b['sources'].pop('KE02.lean')
        variants.append(b)
        b = copy.deepcopy(self.binding)
        b['sources']['KE02/Fixture.lean'] = 'not a hash'
        variants.append(b)
        for index, binding in enumerate(variants):
            with self.subTest(case=index):
                self.set_manifest(json.dumps(binding).encode())
                self.rejected(v.check_sources, 'Invalid|inventory|Missing aggregate', self.root)

    def test_missing_bound_source(self):
        (self.root / 'KE02/Fixture.lean').unlink()
        self.rejected(v.check_sources, 'source inventory', self.root)

    def test_missing_bound_configuration(self):
        (self.root / 'lean-toolchain').unlink()
        self.rejected(v.check_sources, 'Missing file', self.root)

    def test_tampered_source(self):
        self.write('KE02/Fixture.lean', 'theorem changed : True := by trivial\n')
        self.rejected(v.check_sources, 'Bound file changed', self.root)

    def test_tampered_configuration(self):
        self.write('lakefile.toml', 'name = "wrong"\n')
        self.rejected(v.check_sources, 'Bound file changed', self.root)

    def test_rebound_fixed_statement_still_rejected(self):
        name = 'KE02/SelectorStatement.lean'
        self.write(name, (self.root / name).read_bytes() + b'\n-- harmless change still violates freeze\n')
        self.rebind()
        self.rejected(v.check_sources, 'Fixed statement changed', self.root)

    def test_extra_lean_even_outside_module_directory(self):
        self.write('notes/Unexpected.lean', 'theorem unexpected : True := by trivial\n')
        self.rejected(v.check_sources, 'source inventory', self.root)

    def test_changed_axiom_probe(self):
        self.write('audit/Axioms.lean', 'import KE02\n#print axioms True.intro\n')
        self.rejected(v.check_sources, 'Axiom probe changed', self.root)

    def test_fixed_source_symlink(self):
        source = self.root / 'KE02/Fixture.lean'
        outside = Path(self.temp.name) / 'copy.lean'
        outside.write_bytes(source.read_bytes())
        source.unlink()
        source.symlink_to(outside)
        self.rejected(v.check_sources, 'symlink|Linked', self.root)

    def test_symlinked_configuration_and_directory(self):
        source = self.root / 'README.md'
        outside = Path(self.temp.name) / 'README-copy.md'
        outside.write_bytes(source.read_bytes())
        source.unlink()
        source.symlink_to(outside)
        self.rejected(v.check_sources, 'symlink|Linked', self.root)

    def test_unrelated_symlink_directory_is_rejected(self):
        (self.root / 'linked').symlink_to(Path(self.temp.name), target_is_directory=True)
        self.rejected(v.check_sources, 'symlink', self.root)

    def test_forbidden_metaprogramming_and_directives(self):
        tokens = ['sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'native_eval',
                  'ofReduceBool', 'implemented_by', 'extern', 'initialize', 'builtin_initialize',
                  'elab', 'elab_rules', 'macro', 'macro_rules', 'syntax', 'run_tac', 'run_elab',
                  'eval_expr', 'Lean.Environment.add', 'setReducibilityStatus', '#eval 1',
                  'set_option debug.skipKernelTC true', 'set_option pp.all true',
                  'set_option trace.Meta.Tactic.simp true']
        for token in tokens:
            with self.subTest(token=token):
                self.write('KE02/Fixture.lean', '-- ' + token + '\n')
                self.rebind()
                self.rejected(v.check_sources, 'Disallowed', self.root)

    def test_safe_options_and_ordinary_kernel_tactics(self):
        v.reject_forbidden('set_option maxHeartbeats 400000 in\n'
                           'theorem t : 1 = 1 := by decide\n', 'fixture')

    def test_invalid_source_encoding(self):
        self.write('KE02/Fixture.lean', b'\xff')
        self.rebind()
        self.rejected(v.check_sources, 'Invalid source encoding', self.root)

    def test_missing_extra_and_modified_helpers(self):
        helper = sorted(v.HELPERS)[0]
        original = (self.root / helper).read_bytes()
        self.write(helper, original + b'# tamper\n')
        self.rejected(v.check_helpers, 'helper changed', self.root)
        self.write(helper, original)
        (self.root / helper).unlink()
        self.rejected(v.check_helpers, 'helper inventory', self.root)
        self.write(helper, original)
        self.write('audit/extra.py', '# extra\n')
        self.rejected(v.check_helpers, 'helper inventory', self.root)

    def test_unfrozen_helpers_rejected(self):
        with patch.object(v, 'HELPER_HASHES', {}):
            self.rejected(v.check_helpers, 'not frozen', self.root)

    def test_local_import_cycle_and_missing_import(self):
        for sources, expected in [
            ({'KE02.lean': b'import KE02.Absent\n'}, 'Missing local import'),
            ({'KE02.lean': b'import KE02.Foo\n', 'KE02/Foo.lean': b'import KE02\n'}, 'Import cycle')]:
            with self.subTest(expected=expected):
                self.rejected(v.module_order, expected, sources)

    def test_exact_axiom_output_fixed(self):
        self.assertEqual(v.parse_axioms(GOOD_AXIOMS), sorted(v.EXPECTED_AXIOMS))

    def test_forged_incomplete_or_extra_axiom_output(self):
        bad = ['', GOOD_AXIOMS + 'PASS\n', 'warning\n' + GOOD_AXIOMS,
               GOOD_AXIOMS + GOOD_AXIOMS, GOOD_AXIOMS.replace('coreCertificate', 'anotherTheorem'),
               GOOD_AXIOMS.replace('Quot.sound', 'sorryAx'),
               GOOD_AXIOMS.replace('Quot.sound', 'Classical.choice'),
               GOOD_AXIOMS.replace(', Quot.sound', ''),
               GOOD_AXIOMS.replace('Quot.sound', 'Quot.sound, localAxiom'),
               'PASS: exact standard axiom set.\n']
        for output in bad:
            with self.subTest(output=output):
                self.rejected(v.parse_axioms, 'axiom|axioms', output)
        self.rejected(v.parse_axioms, 'standard error', GOOD_AXIOMS, 'warning\n')

    def test_real_process_failure_overrides_plausible_stdout(self):
        code = 'import sys; print(' + repr(GOOD_AXIOMS) + '); sys.exit(7)'
        self.rejected(v.run_checked, 'status 7', [sys.executable, '-I', '-c', code], self.root)

    def test_process_launch_timeout_and_decode_failures(self):
        failures = [OSError('cannot execute'), subprocess.TimeoutExpired('lean', 1),
                    UnicodeDecodeError('utf8', b'\xff', 0, 1, 'invalid')]
        for failure in failures:
            with self.subTest(kind=type(failure).__name__), patch.object(v.subprocess, 'run', side_effect=failure):
                self.rejected(v.run_checked, 'could not complete', ['lean'], self.root)

    def test_default_process_environment_drops_injected_paths(self):
        names = ['LEAN_PATH', 'LEAN_SYSROOT', 'PYTHONPATH', 'GIT_CONFIG', 'LD_PRELOAD']
        code = 'import json,os; print(json.dumps({k:os.environ.get(k) for k in ' + repr(names) + '}))'
        with patch.dict(os.environ, {name: '/untrusted/injection' for name in names}):
            result = v.run_checked([sys.executable, '-I', '-c', code], self.root)
        self.assertEqual(json.loads(result.stdout), {name: None for name in names})

    def test_lake_resolution_uses_clean_environment_and_pinned_binary(self):
        self.lean.parent.mkdir(parents=True)
        self.lean.write_bytes(b'fixture compiler')
        prefix = self.lean.parent.parent
        result = subprocess.CompletedProcess([], 0, str(prefix) + '\n', '')
        injection = {name: '/untrusted/injection' for name in
                     ['LEAN_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN', 'LAKE_HOME',
                      'PYTHONPATH', 'LD_PRELOAD', 'GIT_CONFIG']}
        with patch.object(v.shutil, 'which', return_value='/fixture/bin/lake'), \
                patch.object(v, 'LEAN_SHA256', v.sha(self.lean.read_bytes())), \
                patch.object(v, 'run_checked', return_value=result) as run, \
                patch.dict(os.environ, injection):
            self.assertEqual(v.resolve_compiler(self.root), self.lean.resolve())
        argv, root, environment = run.call_args.args
        self.assertEqual(argv, ['/fixture/bin/lake', '--no-build', 'env', 'lean', '--print-prefix'])
        self.assertEqual(root, self.root)
        self.assertEqual(environment['PATH'], '/fixture/bin' + os.pathsep + os.defpath)
        for name in injection:
            self.assertNotIn(name, environment)

    def test_lake_resolution_rejects_missing_launcher(self):
        with patch.object(v.shutil, 'which', return_value=None):
            self.rejected(v.resolve_compiler, 'unavailable', self.root)

    def test_lake_resolution_rejects_malformed_or_missing_compiler(self):
        cases = [('', '', 'Malformed'), ('relative/path\n', '', 'not absolute'),
                 ('/one\n/two\n', '', 'Malformed'), (' /one\n', '', 'Malformed'),
                 (str(Path(self.temp.name) / 'missing') + '\n', '', 'missing'),
                 ('/one\n', 'warning\n', 'standard error')]
        for stdout, stderr, diagnostic in cases:
            with self.subTest(stdout=stdout, stderr=stderr), \
                    patch.object(v.shutil, 'which', return_value='/fixture/bin/lake'), \
                    patch.object(v, 'run_checked', return_value=
                                 subprocess.CompletedProcess([], 0, stdout, stderr)):
                self.rejected(v.resolve_compiler, diagnostic, self.root)

    def test_lake_resolution_rejects_wrong_binary(self):
        self.lean.parent.mkdir(parents=True)
        self.lean.write_bytes(b'wrong compiler')
        result = subprocess.CompletedProcess([], 0, str(self.lean.parent.parent) + '\n', '')
        with patch.object(v.shutil, 'which', return_value='/fixture/bin/lake'), \
                patch.object(v, 'run_checked', return_value=result):
            self.rejected(v.resolve_compiler, 'Compiler digest differs', self.root)

    def test_lake_resolution_propagates_failed_process(self):
        with patch.object(v.shutil, 'which', return_value='/fixture/bin/lake'), \
                patch.object(v.subprocess, 'run', return_value=
                             subprocess.CompletedProcess([], 7, '/plausible/prefix\n', '')):
            self.rejected(v.resolve_compiler, 'Process failed with status 7', self.root)

    def tiny_dependency_snapshot(self, scenario='success'):
        toolchain = Path(self.temp.name) / 'toolchain'
        lean = toolchain / 'bin/lean'
        lean.parent.mkdir(parents=True)
        lean.write_bytes(b'fixture compiler')
        runtime = toolchain / 'lib/lean/Init.olean'
        runtime.parent.mkdir(parents=True)
        runtime.write_bytes(b'fixture runtime')
        dep = self.root / '.lake/packages/fixture'
        lib = dep / '.lake/build/lib/lean'
        lib.mkdir(parents=True)
        artifact = lib / 'Ordinary.olean'
        artifact.write_bytes(b'fixture dependency')
        self.write('lake-manifest.json', json.dumps({'packages': [{'name': 'fixture', 'rev': 'a' * 40}]}))
        if scenario == 'linked_cache_artifact':
            (lib / 'Linked.olean').symlink_to(artifact)
        elif scenario == 'shadowed_local_module':
            (lib / 'KE02.olean').write_bytes(b'stale local theorem')
        elif scenario == 'shadowed_local_directory':
            (lib / 'KE02').mkdir()
            (lib / 'KE02/Statement.olean').write_bytes(b'stale local theorem')
        elif scenario == 'toolchain_link_escape':
            outside = Path(self.temp.name) / 'outside.olean'
            outside.write_bytes(b'outside runtime')
            (runtime.parent / 'Escape.olean').symlink_to(outside)

        def fake_command(argv, cwd, *args, **kwargs):
            if '--version' in argv:
                text = 'Lean 4.34.0-rc2, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d'
                if scenario == 'wrong_version':
                    text = 'Lean 4.0.0, unexpected commit'
            elif 'rev-parse' in argv:
                self.assertEqual(argv[0], '/usr/bin/git')
                text = ('b' if scenario == 'wrong_revision' else 'a') * 40 + '\n'
            elif 'status' in argv:
                text = ' M Mathlib.lean\n' if scenario == 'dirty_dependency' else ''
            else:
                raise RuntimeError('Unexpected dependency command: ' + repr(argv))
            return subprocess.CompletedProcess(argv, 0, text, '')

        digest = '0' * 64 if scenario == 'wrong_compiler_hash' else v.sha(lean.read_bytes())
        with patch.object(v, 'LEAN_SHA256', digest), \
                patch.object(v, 'run_checked', side_effect=fake_command):
            return v.dependency_snapshot(self.root, lean)

    def test_tiny_dependency_positive_control_hashes_runtime_and_objects(self):
        snapshot, libraries = self.tiny_dependency_snapshot()
        self.assertIn('lean/Init.olean', snapshot['toolchain_libraries'])
        self.assertIn('Ordinary.olean', snapshot['packages']['fixture']['files'])
        self.assertEqual(len(libraries), 1)

    def test_wrong_compiler_digest_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'Compiler digest differs', 'wrong_compiler_hash')

    def test_wrong_compiler_version_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'Compiler version differs', 'wrong_version')

    def test_wrong_dependency_revision_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'revision differs', 'wrong_revision')

    def test_dirty_dependency_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'sources dirty', 'dirty_dependency')

    def test_linked_cache_artifact_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'Linked cache artifact', 'linked_cache_artifact')

    def test_cached_local_aggregate_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'shadowed in cache', 'shadowed_local_module')

    def test_cached_local_module_directory_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'shadowed in cache', 'shadowed_local_directory')

    def test_toolchain_runtime_link_escape_is_rejected(self):
        self.rejected(self.tiny_dependency_snapshot, 'outside installed toolchain', 'toolchain_link_escape')

    def test_cli_default_output_matches_matrix_command(self):
        with patch.object(sys, 'argv', ['audit/verify.py']), patch.object(v, 'verify') as verify:
            self.assertEqual(v.main(), 0)
            verify.assert_called_once_with(Path('.audit-build'))

    def test_cli_explicit_output_is_preserved(self):
        with patch.object(sys, 'argv', ['audit/verify.py', '--output', 'fresh-build']), \
                patch.object(v, 'verify') as verify:
            self.assertEqual(v.main(), 0)
            verify.assert_called_once_with(Path('fresh-build'))

    def test_cli_default_rejects_preexisting_output(self):
        (self.root / '.audit-build').mkdir()
        error = io.StringIO()
        with patch.object(sys, 'argv', ['audit/verify.py']), \
                patch.object(v, 'verify', side_effect=lambda output:
                    v.prepare_output(self.root / output, self.root, self.lean)), \
                contextlib.redirect_stderr(error):
            self.assertEqual(v.main(), 1)
        self.assertEqual(error.getvalue(), 'FAIL: Build output already exists\n')

    def test_cli_unknown_and_missing_value_arguments_fail(self):
        for arguments in (['--unknown'], ['--output'], ['unexpected']):
            with self.subTest(arguments=arguments), \
                    patch.object(sys, 'argv', ['audit/verify.py', *arguments]), \
                    patch.object(v, 'verify') as verify, contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as caught:
                v.main()
            self.assertEqual(caught.exception.code, 2)
            verify.assert_not_called()

    def test_stale_output_directory_is_rejected(self):
        output = self.root / 'existing'
        output.mkdir()
        (output / 'stale.olean').write_bytes(b'old object')
        self.rejected(v.prepare_output, 'already exists', output, self.root, self.lean)

    def test_output_cannot_overlap_development_cache(self):
        self.rejected(v.prepare_output, 'overlaps', self.root / '.lake/new', self.root, self.lean)

    def test_output_traversal_cannot_overlap_development_cache(self):
        (self.root / 'outer').mkdir()
        self.rejected(v.prepare_output, 'overlaps', self.root / 'outer/../.lake/new', self.root, self.lean)

    def test_symlink_output_parent_is_rejected(self):
        (self.root / 'linked').symlink_to(Path(self.temp.name), target_is_directory=True)
        self.rejected(v.prepare_output, 'linked|symlink', self.root / 'linked/new', self.root, self.lean)

    def test_symlink_hidden_by_output_traversal_is_rejected(self):
        target = self.root / 'target'
        target.mkdir()
        (self.root / 'linked').symlink_to(target, target_is_directory=True)
        self.rejected(v.prepare_output, 'linked|symlink', self.root / 'linked/../new', self.root, self.lean)

    def test_output_cannot_overlap_resolved_dependency_root(self):
        dep = Path(self.temp.name) / 'dependency'
        dep.mkdir()
        cache = self.root / '.lake/packages'
        cache.mkdir(parents=True)
        (cache / 'fixture').symlink_to(dep, target_is_directory=True)
        self.rejected(v.prepare_output, 'dependency cache', dep / 'new-output', self.root, self.lean)

    def test_output_cannot_overlap_toolchain(self):
        toolchain = Path(self.temp.name) / 'toolchain'
        (toolchain / 'bin').mkdir(parents=True)
        self.rejected(v.prepare_output, 'toolchain', toolchain / 'new-output',
                      self.root, toolchain / 'bin/lean')

    def simulated_verify(self, scenario='success'):
        output = Path(self.temp.name) / 'build'
        commands = []
        dependency = {'compiler': 'fixture', 'version': 'fixture', 'packages': {}}
        dep_calls = 0

        def fake_dependencies(_, lean):
            nonlocal dep_calls
            dep_calls += 1
            result = copy.deepcopy(dependency)
            if scenario == 'changed_dependencies' and dep_calls == 2:
                result['version'] = 'changed'
            return result, []

        def fake_run(argv, **kwargs):
            commands.append((list(argv), kwargs.get('env')))
            stdout, stderr, code = '', '', 0
            if '-o' in argv:
                target = Path(argv[argv.index('-o') + 1])
                if scenario != 'missing_object':
                    target.write_bytes(b'' if scenario == 'empty_object' else b'fresh simulated object')
                if scenario == 'compile_stderr':
                    stderr = 'compiler warning\n'
                if scenario == 'compile_failed_with_object':
                    code, stdout = 1, GOOD_AXIOMS
            elif str(argv[-1]).endswith('Axioms.lean'):
                stdout = GOOD_AXIOMS
                if scenario == 'probe_failed_with_good_output':
                    code = 1
                elif scenario == 'probe_stderr':
                    stderr = 'warning\n'
                elif scenario == 'probe_forged_output':
                    stdout = GOOD_AXIOMS + 'PASS\n'
                elif scenario == 'source_changed_during_build':
                    self.write('KE02/Fixture.lean', 'theorem replaced : True := by trivial\n')
                elif scenario == 'helper_changed_during_build':
                    self.write('audit/check_exact.py', '# replaced helper\n')
                elif scenario == 'verifier_changed_during_build':
                    self.write('audit/verify.py', '# replaced verifier\n')
            elif str(argv[-1]).endswith('check_exact.py'):
                stdout = '{"status": "PASS"}\n'
                if scenario == 'screen_failed_with_good_output':
                    code = 1
                elif scenario == 'screen_fail_status':
                    stdout = '{"status": "FAIL"}\n'
                elif scenario == 'screen_stderr':
                    stderr = 'warning\n'
            else:
                raise RuntimeError('Unexpected simulated process: ' + repr(argv))
            return subprocess.CompletedProcess(argv, code, stdout, stderr)

        with patch.object(v, 'resolve_compiler', return_value=self.lean), \
                patch.object(v, 'dependency_snapshot', side_effect=fake_dependencies), \
                patch.object(v.subprocess, 'run', side_effect=fake_run), \
                contextlib.redirect_stdout(io.StringIO()):
            receipt = v.verify(output, self.root)
        return receipt, output, commands

    def test_orchestration_positive_control_uses_fresh_isolated_objects(self):
        receipt, output, commands = self.simulated_verify()
        self.assertEqual(receipt['status'], 'PASS')
        self.assertEqual(receipt['build_mode'], 'clean')
        self.assertTrue(receipt['project_objects_initially_empty'])
        self.assertTrue((output / 'BUILD_RECEIPT.json').is_file())
        for argv, env in commands:
            if argv[0] == str(self.lean):
                self.assertEqual(env['LEAN_PATH'], str(output / 'objects'))
                self.assertEqual(env['LEAN_NUM_THREADS'], '1')
                self.assertNotIn(str(self.root / '.lake/build'), env['LEAN_PATH'])

    def test_orchestration_rejects_failed_compile_despite_object_and_output(self):
        self.rejected(self.simulated_verify, 'Process failed', 'compile_failed_with_object')

    def test_orchestration_rejects_missing_object(self):
        self.rejected(self.simulated_verify, 'Missing compiled module', 'missing_object')

    def test_orchestration_rejects_empty_object(self):
        self.rejected(self.simulated_verify, 'Missing compiled module', 'empty_object')

    def test_orchestration_rejects_compiler_stderr(self):
        self.rejected(self.simulated_verify, 'Compiler standard error', 'compile_stderr')

    def test_orchestration_rejects_failed_probe_despite_good_output(self):
        self.rejected(self.simulated_verify, 'Process failed', 'probe_failed_with_good_output')

    def test_orchestration_rejects_forged_probe_output(self):
        self.rejected(self.simulated_verify, 'axiom output', 'probe_forged_output')

    def test_orchestration_rejects_probe_stderr(self):
        self.rejected(self.simulated_verify, 'standard error', 'probe_stderr')

    def test_orchestration_rejects_failed_screen_despite_good_output(self):
        self.rejected(self.simulated_verify, 'Process failed', 'screen_failed_with_good_output')

    def test_orchestration_rejects_screen_fail_status(self):
        self.rejected(self.simulated_verify, 'Python audit child output mismatch', 'screen_fail_status')

    def test_orchestration_rejects_screen_stderr(self):
        self.rejected(self.simulated_verify, 'Python audit child output mismatch', 'screen_stderr')

    def test_orchestration_rejects_changed_source(self):
        self.rejected(self.simulated_verify, 'Bound file changed', 'source_changed_during_build')

    def test_orchestration_rejects_changed_helper(self):
        self.rejected(self.simulated_verify, 'Python audit child source mismatch', 'helper_changed_during_build')

    def test_orchestration_rejects_changed_verifier(self):
        self.rejected(self.simulated_verify, 'implementation changed', 'verifier_changed_during_build')

    def test_orchestration_rejects_changed_dependencies(self):
        self.rejected(self.simulated_verify, 'Dependencies changed', 'changed_dependencies')


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(VerifierControls)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
