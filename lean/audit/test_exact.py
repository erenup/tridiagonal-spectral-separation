#!/usr/bin/env python3
"""Black-box regression tests for the exact checker, using only the stdlib.

Every case runs as an ordinary and an optimized child interpreter.  Pinning the
substantive rejection text prevents the final unknown-control guard from making
an accidentally passing negative control look successful.
"""
from pathlib import Path
import json
import os
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "audit" / "check_exact.py"
MODES = {"normal": [], "optimized": ["-O"]}
NEGATIVE_CONTROLS = {
    "unordered": "unordered roots violate upper bound",
    "nonpositive": "nonpositive root violates positivity",
    "wrong_graeffe": "corrupted transformed coefficient",
    "bad_reply": "reply contract",
}
UNKNOWN_CONTROL = "unknown_control"
CASES = {
    "positive": [],
    **{name: [name] for name in NEGATIVE_CONTROLS},
    "unknown": [UNKNOWN_CONTROL],
    "excess_arguments": ["unordered", "nonpositive"],
}
EXPECTED_POSITIVE = {
    "status": "PASS",
    "graeffe_identities": 30,
    "coefficient_cases": 60,
    "selector_cases": 27,
    "selector_transcripts": (
        [{"n": 2, "rounds": 7, "calls": 56}] * 9
        + [{"n": 5, "rounds": 11, "calls": 88}] * 9
        + [{"n": 9, "rounds": 14, "calls": 112}] * 9
    ),
}


class ExactCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.results = {}
        cls.commands = {}
        environment = {
            "PATH": os.defpath,
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PYTHONHASHSEED": "0",
        }
        for mode, flags in MODES.items():
            for case, arguments in CASES.items():
                command = [sys.executable, *flags, "-S", "-s", "-B", str(CHECKER), *arguments]
                cls.commands[mode, case] = command
                cls.results[mode, case] = subprocess.run(
                    command, cwd=ROOT, env=environment, capture_output=True,
                    check=False, timeout=60,
                )

    def check_rejection(self, case, diagnostic):
        for mode in MODES:
            with self.subTest(mode=mode, case=case):
                result = self.results[mode, case]
                self.assertEqual(result.returncode, 1)
                self.assertEqual(result.stdout, b"")
                self.assertEqual(result.stderr, (diagnostic + "\n").encode("utf-8"))

    def test_full_positive_transcript(self):
        expected_bytes = (json.dumps(EXPECTED_POSITIVE, sort_keys=True) + "\n").encode("utf-8")
        for mode in MODES:
            with self.subTest(mode=mode):
                result = self.results[mode, "positive"]
                self.assertEqual(result.returncode, 0)
                self.assertEqual(result.stderr, b"")
                self.assertEqual(json.loads(result.stdout), EXPECTED_POSITIVE)
                self.assertEqual(result.stdout, expected_bytes)

    def test_unordered_control(self):
        self.check_rejection("unordered", NEGATIVE_CONTROLS["unordered"])

    def test_nonpositive_control(self):
        self.check_rejection("nonpositive", NEGATIVE_CONTROLS["nonpositive"])

    def test_wrong_graeffe_control(self):
        self.check_rejection("wrong_graeffe", NEGATIVE_CONTROLS["wrong_graeffe"])

    def test_bad_reply_control(self):
        self.check_rejection("bad_reply", NEGATIVE_CONTROLS["bad_reply"])

    def test_unknown_control_fails_closed(self):
        self.check_rejection("unknown", "unknown or unexpectedly passing negative control")

    def test_extra_arguments_fail_closed(self):
        self.check_rejection("excess_arguments", "usage: check_exact.py [negative-control]")

    def test_normal_optimized_byte_parity(self):
        for case in CASES:
            with self.subTest(case=case):
                normal = self.results["normal", case]
                optimized = self.results["optimized", case]
                self.assertEqual(normal.returncode, optimized.returncode)
                self.assertEqual(normal.stdout, optimized.stdout)
                self.assertEqual(normal.stderr, optimized.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
