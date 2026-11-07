#!/usr/bin/env python3
"""Tamper controls for audit/verify.py (standard library only).

The output lists the passing controls in a fixed order and contains no
timing, so it is identical under `python -O`.
"""

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify  # noqa: E402


VALID_OUTPUT = ("'KE02.coreCertificate' depends on axioms: "
                "[propext, Classical.choice, Quot.sound]\n")
NEGATIVE_SOURCE = ("import KE02\n\n"
                   "example : True := trivial\n\n"
                   "example : False := by\n  trivial\n")


class AuditControls(unittest.TestCase):

    def fixture(self):
        """A copy of every bound file in a fresh directory inside `.lake`."""
        base = verify.ROOT / ".lake"
        temporary = tempfile.TemporaryDirectory(prefix="audit-control-", dir=base)
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        manifest = json.loads((verify.ROOT / verify.SOURCE_HASHES_PATH).read_text("utf-8"))
        names = (set(manifest["sources"]) | set(manifest["configuration"])
                 | {verify.SOURCE_HASHES_PATH, verify.STATEMENT_HASHES_PATH})
        for name in names:
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((verify.ROOT / name).read_bytes())
        return root

    def check(self, root):
        return verify.check_statements(root, verify.check_sources(root))

    def test_valid_fixture(self):
        root = self.fixture()
        snapshot = self.check(root)
        self.assertIn("KE02/Statement.lean", snapshot)
        modules = verify.module_order(snapshot)
        self.assertEqual(modules[-1], "KE02")
        self.assertEqual(verify.parse_axioms(VALID_OUTPUT),
                         ["propext", "Classical.choice", "Quot.sound"])

    def test_forbidden_tokens_and_commands(self):
        for source in (
            "theorem bad : False := by sorry",
            "theorem bad : False := by\n  admit",
            "axiom bad : False",
            "theorem bad : False := sorryAx _ false",
            "unsafe def bad : Nat := 0",
            "example : 1 = 1 := by native_decide",
            "@[implemented_by f] def g : Nat := 0",
            "@[extern \"c\"] def g : Nat := 0",
            "opaque c : Nat",
            "theorem t : True := Lean.ofReduceBool _ _ rfl",
            "set_option maxHeartbeats 0 in\ntheorem t : True := trivial",
            "macro \"x\" : term => `(1)",
            "elab \"x\" : term => pure default",
            "run_cmd pure ()",
            "#eval 1",
            "  #exit",
            "#print axioms KE02.coreCertificate",
            "/- sorry -/ theorem t : True := trivial",
            "def s := \"admit\"",
            "notation \"x\" => 1",
            "infixl:65 \" +' \" => HAdd.hAdd",
            "infix:50 \" ~ \" => Eq",
            "infixr:67 \" :: \" => List.cons",
            "prefix:max \"√\" => Real.sqrt",
            "postfix:max \"!\" => Nat.factorial",
            "instance : Inhabited Nat := ⟨0⟩",
            "attribute [simp] Nat.add_comm",
            "export Nat (succ)",
            "partial def f : Nat → Nat := f",
            "theorem t : True := trivial #exit",
            "/- #print axioms t -/",
        ):
            with self.subTest(source=source), self.assertRaises(verify.AuditError):
                verify.reject_forbidden(source, "KE02/Example.lean")
        verify.reject_forbidden("/-!\n# Heading\n-/\ntheorem t : True := trivial\n",
                                "KE02/Example.lean")
        verify.reject_forbidden("theorem partial_sum : True := List.prefix_refl [] ▸ trivial\n",
                                "KE02/Example.lean")
        verify.reject_forbidden(verify.AXIOMS_SOURCE, verify.AXIOMS_PATH)

    def test_changed_source_rejected(self):
        for name in ("KE02/EndpointProof.lean", "KE02/Algorithm2Proof.lean",
                     "audit/Probes.lean", "audit/probes/WrongTieRule.lean"):
            root = self.fixture()
            path = root / name
            path.write_bytes(path.read_bytes() + b"\n-- changed\n")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                self.check(root)

    def test_missing_source_rejected(self):
        for name in ("KE02/WronskianProof.lean", "KE02.lean", "audit/Axioms.lean",
                     "audit/probes/MissingAccuracy.lean"):
            root = self.fixture()
            (root / name).unlink()
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                self.check(root)

    def test_extra_source_rejected(self):
        for name in ("KE02/Extra.lean", "KE02/Nested/Extra.lean", "Extra.lean",
                     "audit/probes/Extra.lean"):
            root = self.fixture()
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("theorem extra : True := trivial\n", encoding="utf-8")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                self.check(root)

    def test_dependency_directory_excluded(self):
        root = self.fixture()
        dependency = root / ".lake" / "packages" / "Dependency.lean"
        dependency.parent.mkdir(parents=True)
        dependency.write_text("axiom dependency : False\n", encoding="utf-8")
        self.assertNotIn(".lake/packages/Dependency.lean", self.check(root))

    def test_symlinks_rejected(self):
        for directory in (False, True):
            root = self.fixture()
            target = root / "KE02" if directory else root / "KE02.lean"
            link = root / ("Linked" if directory else "Linked.lean")
            link.symlink_to(target, target_is_directory=directory)
            with self.subTest(directory=directory), self.assertRaises(verify.AuditError):
                self.check(root)
        root = self.fixture()
        path = root / "KE02" / "Statement.lean"
        path.unlink()
        path.symlink_to(verify.ROOT / "KE02" / "Statement.lean")
        with self.assertRaises(verify.AuditError):
            self.check(root)

    def test_statement_files_cannot_be_commented_out(self):
        for name in sorted(verify.STATEMENT_FILES):
            root = self.fixture()
            path = root / name
            path.write_text("/-\n" + path.read_text(encoding="utf-8") + "\n-/\n",
                            encoding="utf-8")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                self.check(root)

    def test_statement_manifest_must_agree(self):
        root = self.fixture()
        snapshot = verify.check_sources(root)
        path = root / verify.STATEMENT_HASHES_PATH
        manifest = json.loads(path.read_text("utf-8"))
        changed = dict(manifest["statements"])
        changed["KE02/Statement.lean"] = "0" * 64
        missing = dict(manifest["statements"])
        del missing["KE02/Algorithm2Statement.lean"]
        for statements in (changed, missing):
            raw = json.dumps({"schema": 1, "statements": statements}).encode("utf-8")
            path.write_bytes(raw)
            with self.subTest(size=len(statements)), mock.patch.object(
                    verify, "STATEMENT_HASHES_SHA256", hashlib.sha256(raw).hexdigest()):
                with self.assertRaises(verify.AuditError):
                    verify.check_statements(root, snapshot)

    def test_manifests_are_pinned(self):
        for name in (verify.SOURCE_HASHES_PATH, verify.STATEMENT_HASHES_PATH):
            root = self.fixture()
            path = root / name
            path.write_bytes(path.read_bytes() + b"\n")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                self.check(root)
            path.unlink()
            path.symlink_to(verify.ROOT / name)
            with self.subTest(name=name, linked=True), self.assertRaises(verify.AuditError):
                self.check(root)

    def test_malformed_manifest_fails_closed(self):
        digest = '"' + "a" * 64 + '"'
        for raw in (
            b"[]", b"{}", b"not JSON", b"\xff",
            b'{"schema":1,"schema":1,"sources":{},"configuration":{}}',
            ('{"schema":true,"sources":{"KE02.lean":' + digest + '},"configuration":{}}').encode(),
            b'{"schema":1,"sources":{},"configuration":{}}',
            ('{"schema":1,"sources":{"../KE02.lean":' + digest + '},'
             '"configuration":{"lakefile.toml":' + digest + '}}').encode(),
            b'{"schema":1,"sources":{"KE02.lean":"wrong"},"configuration":{}}',
        ):
            root = self.fixture()
            (root / verify.SOURCE_HASHES_PATH).write_bytes(raw)
            with self.subTest(raw=raw), mock.patch.object(
                    verify, "SOURCE_HASHES_SHA256", hashlib.sha256(raw).hexdigest()):
                with self.assertRaises(verify.AuditError):
                    verify.check_sources(root)

    def test_configuration_tamper_rejected(self):
        for name in sorted(verify.CONFIGURATION_FILES):
            root = self.fixture()
            path = root / name
            path.write_bytes(path.read_bytes() + b"\n# changed\n")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                self.check(root)

    def test_forged_axiom_probe_rejected(self):
        root = self.fixture()
        (root / verify.AXIOMS_PATH).write_text(
            '#eval IO.println "' + VALID_OUTPUT.strip() + '"\n', encoding="utf-8")
        with self.assertRaises(verify.AuditError):
            self.check(root)

    def test_axiom_output_parsing(self):
        self.assertEqual(verify.parse_axioms(VALID_OUTPUT.replace(
            "propext, Classical.choice, Quot.sound", "Quot.sound, propext, Classical.choice")),
            ["Quot.sound", "propext", "Classical.choice"])
        for output in (
            "", "Build completed successfully.\n", VALID_OUTPUT + VALID_OUTPUT,
            "note\n" + VALID_OUTPUT, VALID_OUTPUT + "extra\n", VALID_OUTPUT.rstrip("\n"),
            VALID_OUTPUT.replace("coreCertificate", "otherTheorem"),
            VALID_OUTPUT.replace("]", ", sorryAx]"),
            VALID_OUTPUT.replace(", Quot.sound", ""),
            VALID_OUTPUT.replace("Quot.sound", "propext"),
            VALID_OUTPUT.replace("]", ", Lean.ofReduceBool]"),
            VALID_OUTPUT.replace("[propext, Classical.choice, Quot.sound]", "[]"),
            "'KE02.coreCertificate' does not depend on any axioms\n",
        ):
            with self.subTest(output=output), self.assertRaises(verify.AuditError):
                verify.parse_axioms(output)
        with self.assertRaises(verify.AuditError):
            verify.parse_axioms(VALID_OUTPUT, "warning: unexpected\n")

    def test_negative_probe_classification(self):
        error = "audit/probes/P.lean:{}:2: error: Type mismatch\n"
        kind = "Type mismatch"
        self.assertEqual(
            verify.classify_negative("P", NEGATIVE_SOURCE, 1, error.format(5), kind), 5)
        self.assertEqual(
            verify.classify_negative("P", NEGATIVE_SOURCE, 1, error.format(6), kind), 6)
        for returncode, output, expected in (
            (0, "", kind), (0, error.format(5), kind), (1, "", kind), (1, "warning only\n", kind),
            (1, error.format(3), kind), (1, error.format(1) + error.format(5), kind),
            (1, error.format(5), "unsolved goals"),
            (1, error.format(5), "Tactic `assumption` failed"),
            (1, "audit/probes/P.lean:5:2: error: unknown identifier 'x'\n", kind),
        ):
            with self.subTest(returncode=returncode, output=output, expected=expected):
                with self.assertRaises(verify.AuditError):
                    verify.classify_negative("P", NEGATIVE_SOURCE, returncode, output, expected)
        with self.assertRaises(verify.AuditError):
            verify.classify_negative("P", "import KE02\n\nexample : False := by trivial\n", 1,
                                     error.format(3), kind)
        self.assertEqual(sorted(verify.NEGATIVE_PROBES),
                         sorted(name for name in verify.check_sources(verify.ROOT)
                                if verify.PROBE_PATH.fullmatch(name)))

    def test_statement_import_closure(self):
        verify.check_statement_closure(self.check(self.fixture()))
        for sources in (
            {"KE02/Statement.lean": b"import KE02.EndpointProof\n",
             "KE02/EndpointProof.lean": b"import Mathlib.Tactic\n"},
            {"KE02/Statement.lean": b"import KE02.EndpointStatement\n",
             "KE02/EndpointStatement.lean": b"import KE02.Algorithm2Proof\n",
             "KE02/Algorithm2Proof.lean": b"import Mathlib.Tactic\n"},
            {"KE02/Statement.lean": b"import KE02.Missing\n"},
        ):
            with self.subTest(sources=sorted(sources)), self.assertRaises(verify.AuditError):
                verify.check_statement_closure(sources)

    def test_toolchain_outputs_compared_exactly(self):
        verify.check_lean_version(verify.LEAN_VERSION_OUTPUT)
        verify.check_clean_checkout("")
        for output in ("", verify.LEAN_VERSION_OUTPUT.replace("rc2", "rc3"),
                       verify.LEAN_VERSION_OUTPUT.replace("Release", "Debug"),
                       verify.LEAN_VERSION_OUTPUT + "extra\n", "Lean (version 4.34.0-rc2)\n"):
            with self.subTest(output=output), self.assertRaises(verify.AuditError):
                verify.check_lean_version(output)
        with self.assertRaises(verify.AuditError):
            verify.check_lean_version(verify.LEAN_VERSION_OUTPUT, "warning\n")
        for output, stderr in ((" M Mathlib/Order/Basic.lean\n", ""), ("?? extra.lean\n", ""),
                               ("", "fatal: not a git repository\n")):
            with self.subTest(output=output), self.assertRaises(verify.AuditError):
                verify.check_clean_checkout(output, stderr)

    def test_dependency_rebuild_detected(self):
        verify.check_build_output("✔ [3040/3138] Built KE02.EndpointProof (5.0s)\n"
                                  "Build completed successfully (3138 jobs).\n")
        for line in ("✔ [12/3138] Built Mathlib.Analysis.Convex.Slope (9.0s)\n",
                     "✔ [1/3138] Built Batteries.Data.List (1.0s)\n"):
            with self.subTest(line=line), self.assertRaises(verify.AuditError):
                verify.check_build_output(line)

    def test_failed_commands_cannot_pass(self):
        with mock.patch.object(sys, "stderr"):
            with self.assertRaises(verify.AuditError):
                verify.run_checked([sys.executable, "-c",
                                    f"print({VALID_OUTPUT!r}); raise SystemExit(3)"], verify.ROOT)
        with self.assertRaises(verify.AuditError):
            verify.run_checked(["./missing-audit-command"], verify.ROOT)
        result = verify.run_checked([sys.executable, "-c", f"print({VALID_OUTPUT!r}, end='')"],
                                    verify.ROOT)
        self.assertEqual(verify.parse_axioms(result.stdout), ["propext", "Classical.choice",
                                                              "Quot.sound"])

    def test_module_order_and_reachability(self):
        sources = {
            "KE02.lean": b"import KE02.C\n",
            "KE02/A.lean": b"import KE02.B\n",
            "KE02/B.lean": b"import Mathlib.Tactic\n",
            "KE02/C.lean": b"import KE02.A KE02.B -- both\n",
        }
        ordered = verify.module_order(sources)
        self.assertEqual(ordered, ["KE02.B", "KE02.A", "KE02.C", "KE02"])
        for bad in (
            {**sources, "KE02/Unused.lean": b"import KE02.B\n"},
            {"KE02.lean": b"import KE02.Missing\n"},
            {"KE02.lean": b"import KE02.A\n", "KE02/A.lean": b"import KE02\n"},
            {"KE02/A.lean": b"import Mathlib.Tactic\n"},
        ):
            with self.subTest(bad=sorted(bad)), self.assertRaises(verify.AuditError):
                verify.module_order(bad)

    def test_clean_build_directory_is_confined(self):
        root = self.fixture()
        with self.assertRaises(verify.AuditError):
            verify.clean_build_directory(root)
        (root / ".lake").mkdir()
        build = root / ".lake" / "build"
        (build / "lib").mkdir(parents=True)
        (build / "lib" / "object.olean").write_bytes(b"object")
        verify.clean_build_directory(root)
        self.assertFalse(build.exists())
        elsewhere = root / "elsewhere"
        elsewhere.mkdir()
        (elsewhere / "keep").write_bytes(b"keep")
        build.symlink_to(elsewhere, target_is_directory=True)
        with self.assertRaises(verify.AuditError):
            verify.clean_build_directory(root)
        self.assertTrue((elsewhere / "keep").is_file())


class Recorder(unittest.TestResult):
    def __init__(self):
        super().__init__()
        self.passed = []

    def addSuccess(self, test):
        super().addSuccess(test)
        self.passed.append(test.id().rsplit(".", 1)[-1])


def main():
    suite = unittest.TestLoader().loadTestsFromTestCase(AuditControls)
    result = Recorder()
    suite.run(result)
    for name in sorted(result.passed):
        print(f"PASS {name}")
    for test, trace in result.failures + result.errors:
        print(f"FAIL {test.id().rsplit('.', 1)[-1]}")
        print(trace, file=sys.stderr)
    status = "OK" if result.wasSuccessful() else "FAILED"
    print(f"{status}: {result.testsRun} controls, {len(result.passed)} passed")
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
