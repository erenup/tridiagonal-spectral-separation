#!/usr/bin/env python3
"""Runner for the KE-02 exact checks (standard library only).

1. Verifies SHA256SUMS (every file of this folder except SHA256SUMS itself, no unlisted files).
2. Lints the sources: standard-library imports from an allowlist only; no float or complex literals,
   no float()/complex()/pow()/open()/eval()/exec(), no assert statements (they vanish under -O),
   no integer powers with negative literal exponents (they produce floats).
3. Runs each checker in-process and as subprocesses under `-S -s -B` and `-S -s -B -O`, each with
   PYTHONHASHSEED=0 and PYTHONHASHSEED=1, and requires exit status 0, empty stderr and byte-identical
   standard output in all five runs, with the pinned numbers of checks and negative controls.
4. Requires that CHECKERS.txt lists exactly the negative controls that were executed and rejected.
5. Runs its own negative controls: corrupted output, a modified and an unlisted file, a failing
   subprocess, forbidden source constructs, and both checkers with --inject-fault (which must fail).

Usage:  python3 -S -s -B run_checks.py      (also with -O)
Final line on success: RESULT: PASS KE-02 exact checks
"""

import ast
import contextlib
import hashlib
import importlib.util
import io
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKERS = ("check_constants.py", "check_appendix_a.py")
EXPECTED = {"check_constants.py": (208690, 43), "check_appendix_a.py": (2660, 13)}
FLAGS = (("-S", "-s", "-B"), ("-S", "-s", "-B", "-O"))
SEEDS = ("0", "1")
TIMEOUT = 1800
CHECKER_IMPORTS = {"sys", "hashlib", "itertools", "fractions", "math"}
RUNNER_IMPORTS = {"ast", "contextlib", "hashlib", "importlib", "importlib.util", "io", "os", "subprocess", "sys"}
MATH_NAMES = {"isqrt", "comb", "lcm", "gcd"}
FORBIDDEN_NAMES = {"float", "complex", "pow", "open", "eval", "exec", "compile", "input", "__import__",
                   "breakpoint", "__debug__", "globals", "vars"}
FORBIDDEN_ATTRS = {"sqrt", "log", "log2", "log10", "exp", "system", "popen", "urlopen", "connect", "socket"}

sys.dont_write_bytecode = True
LINES = []
FAILED = []


def out(s):
    LINES.append(s)


def passed(s):
    out("PASS: " + s)


def failed(s):
    FAILED.append(s)
    out("FAIL: " + s)


# ---------------------------------------------------------------- SHA256SUMS

def parse_sums(text):
    entries = []
    for line in text.splitlines():
        if not line.strip():
            continue
        parts = line.split("  ", 1)
        if len(parts) != 2 or len(parts[0]) != 64 or any(ch not in "0123456789abcdef" for ch in parts[0]):
            raise ValueError("malformed SHA256SUMS line: " + line)
        name = parts[1]
        if "/" in name or name in (".", "..", "SHA256SUMS"):
            raise ValueError("bad file name in SHA256SUMS: " + name)
        entries.append((parts[0], name))
    return entries


def sums_problems(entries, listing, read):
    """Problems found when the listed hashes are compared with the files `listing` (read via `read`)."""
    probs = []
    names = [n for _, n in entries]
    if len(set(names)) != len(names):
        probs.append("duplicate entries")
    for name in sorted(set(listing) - set(names)):
        probs.append("unlisted file " + name)
    for digest, name in entries:
        if name not in listing:
            probs.append("missing file " + name)
        elif hashlib.sha256(read(name)).hexdigest() != digest:
            probs.append("hash mismatch " + name)
    return probs


def folder_listing():
    names = []
    for name in sorted(os.listdir(HERE)):
        if name in ("SHA256SUMS", "__pycache__"):
            continue
        path = os.path.join(HERE, name)
        if os.path.islink(path) or not os.path.isfile(path):
            names.append(name + " (not a regular file)")
        else:
            names.append(name)
    return names


def read_file(name):
    with open(os.path.join(HERE, name), "rb") as fh:
        return fh.read()


# ---------------------------------------------------------------- lint

def lint(source, allowed_imports):
    probs = []
    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        return ["syntax error: %s" % exc.msg]
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                if a.name not in allowed_imports:
                    probs.append("import " + a.name)
                if a.name == "math":
                    probs.append("import math (only 'from math import isqrt, comb, lcm, gcd')")
        elif isinstance(node, ast.ImportFrom):
            if node.module not in allowed_imports:
                probs.append("from " + str(node.module) + " import")
            if node.module == "math":
                for a in node.names:
                    if a.name not in MATH_NAMES:
                        probs.append("from math import " + a.name)
        elif isinstance(node, ast.Constant) and type(node.value).__name__ in ("float", "complex"):
            probs.append("float or complex literal at line %d" % node.lineno)
        elif isinstance(node, ast.Name) and node.id in FORBIDDEN_NAMES:
            probs.append("forbidden name %s at line %d" % (node.id, node.lineno))
        elif isinstance(node, ast.Attribute) and node.attr in FORBIDDEN_ATTRS:
            probs.append("forbidden attribute %s at line %d" % (node.attr, node.lineno))
        elif isinstance(node, ast.Assert):
            probs.append("assert statement at line %d" % node.lineno)
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
            r = node.right
            if isinstance(r, ast.UnaryOp) and isinstance(r.op, ast.USub) and isinstance(r.operand, ast.Constant) \
                    and isinstance(node.left, ast.Constant):
                probs.append("integer power with a negative exponent at line %d" % node.lineno)
    return probs


LINT_CONTROLS = [
    ("R.N5", "lint: float literal", "x = 0.5\n"),
    ("R.N6", "lint: assert statement", "assert x\n"),
    ("R.N7", "lint: import outside the allowlist", "import os\n"),
    ("R.N8", "lint: float() call", "y = float(3)\n"),
    ("R.N9", "lint: integer power with a negative exponent", "z = 2 ** -1\n"),
    ("R.N10", "lint: open() for writing", "open('f', 'w').write('x')\n"),
    ("R.N11", "lint: import math and math.sqrt", "import math\nw = math.sqrt(2)\n"),
    ("R.N12", "lint: from math import sqrt", "from math import sqrt\n"),
]


# ---------------------------------------------------------------- running

def run_inprocess(name):
    path = os.path.join(HERE, name)
    spec = importlib.util.spec_from_file_location("ke02_inprocess_" + name[:-3], path)
    mod = importlib.util.module_from_spec(spec)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        spec.loader.exec_module(mod)
        code = mod.main([])
    return code, buf.getvalue().encode("ascii"), b""


def run_sub(args, seed):
    env = {"PYTHONHASHSEED": seed, "PATH": os.environ.get("PATH", "/usr/bin:/bin"), "LC_ALL": "C",
           "PYTHONIOENCODING": "ascii"}
    p = subprocess.run([sys.executable] + list(args), cwd=HERE, env=env, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=TIMEOUT, check=False)
    return p.returncode, p.stdout, p.stderr


def is_pass(code, stdout, stderr, name):
    lines = stdout.decode("ascii", "replace").splitlines()
    return (code == 0 and stderr == b"" and len(lines) > 0 and lines[-1].startswith("RESULT: PASS " + name + ":")
            and not any(l.startswith("FAIL:") for l in lines))


def is_fail(code, stdout):
    lines = stdout.decode("ascii", "replace").splitlines()
    return code != 0 and any(l.startswith("FAIL:") for l in lines) and not any(l.startswith("RESULT: PASS") for l in lines)


def counts_of(stdout, name):
    last = stdout.decode("ascii").splitlines()[-1]
    head = "RESULT: PASS " + name + ": "
    if not last.startswith(head):
        return None
    words = last[len(head):].split()
    if len(words) != 6 or words[1] != "checks," or words[3:] != ["negative", "controls", "rejected"]:
        return None
    return int(words[0]), int(words[2])


def controls_of(stdout):
    res = []
    for line in stdout.decode("ascii").splitlines():
        if line.startswith("  control ") and " rejected: " in line:
            cid, desc = line[len("  control "):].split(" rejected: ", 1)
            res.append((cid, desc))
    return res


def parse_checkers_txt(text):
    sections, cur = {}, None
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        if not line.startswith(" "):
            cur = line.strip()
            sections[cur] = []
            continue
        s = line.strip()
        head = s.split("  ", 1)
        if len(head) == 2 and ".N" in head[0] and cur is not None:
            sections[cur].append((head[0], head[1]))
    return sections


# ---------------------------------------------------------------- main

def main():
    out("== run_checks.py: KE-02 exact checks ==")
    if sys.version_info < (3, 11):
        failed("Python 3.11 or later is required")
        return finish()
    own_controls = []

    def control(cid, desc, accepted):
        if accepted is False:
            own_controls.append((cid, desc))
        else:
            failed("negative control %s was accepted: %s" % (cid, desc))

    # 1. SHA256SUMS
    try:
        entries = parse_sums(read_file("SHA256SUMS").decode("ascii"))
        listing = folder_listing()
        probs = sums_problems(entries, listing, read_file)
        if probs:
            failed("SHA256SUMS: " + "; ".join(probs))
        else:
            passed("SHA256SUMS: %d files verified, no unlisted files" % len(entries))
        first = entries[0][1]
        control("R.N2", "SHA256SUMS against a file modified in memory",
                sums_problems(entries, listing, lambda n: read_file(n) + (b"\n" if n == first else b"")) == [])
        control("R.N3", "SHA256SUMS against a folder listing with an unlisted file",
                sums_problems(entries, listing + ["extra.py"], read_file) == [])
    except Exception as exc:
        failed("SHA256SUMS: %s: %s" % (type(exc).__name__, exc))

    # 2. lint
    try:
        probs = []
        for name in CHECKERS:
            probs += [name + ": " + p for p in lint(read_file(name).decode("ascii"), CHECKER_IMPORTS)]
        probs += ["run_checks.py: " + p for p in lint(read_file("run_checks.py").decode("ascii"), RUNNER_IMPORTS)
                  if not p.startswith("forbidden name open")]
        if probs:
            failed("source lint: " + "; ".join(probs[:5]))
        else:
            passed("source lint: checkers import only %s; no float/complex literals or calls, no assert, "
                   "no file or network access" % ", ".join(sorted(CHECKER_IMPORTS)))
        for cid, desc, snippet in LINT_CONTROLS:
            control(cid, desc, lint(snippet, CHECKER_IMPORTS) == [])
    except Exception as exc:
        failed("source lint: %s: %s" % (type(exc).__name__, exc))

    # 3. runs
    executed = {}
    for name in CHECKERS:
        try:
            runs = [("in-process", run_inprocess(name))]
            for flags in FLAGS:
                for seed in SEEDS:
                    runs.append((" ".join(flags) + " PYTHONHASHSEED=" + seed, run_sub(list(flags) + [name], seed)))
            ref = runs[0][1][1]
            out("--- output of %s (identical in all runs) ---" % name)
            for line in ref.decode("ascii").splitlines():
                out(line)
            out("--- end of output of %s ---" % name)
            bad = [label for label, (code, so, se) in runs if not is_pass(code, so, se, name)]
            diff = [label for label, (code, so, se) in runs if so != ref]
            if bad:
                failed("%s: unsuccessful run(s): %s" % (name, ", ".join(bad)))
            if diff:
                failed("%s: output differs from the in-process run: %s" % (name, ", ".join(diff)))
            if not bad and not diff:
                passed("%s: exit status 0, empty stderr and byte-identical output in %d runs (in-process; "
                       "-S -s -B and -S -s -B -O, each with PYTHONHASHSEED=0 and 1)" % (name, len(runs)))
            cnt = counts_of(ref, name)
            if cnt != EXPECTED[name]:
                failed("%s: counts %s differ from the pinned %s" % (name, cnt, EXPECTED[name]))
            else:
                passed("%s: %d checks and %d negative controls, as pinned" % (name, cnt[0], cnt[1]))
            executed[name] = controls_of(ref)
            if name == CHECKERS[0]:
                control("R.N1", "output with one byte changed (byte-identity comparison)",
                        (ref[:-2] + b"X\n") == ref)
        except Exception as exc:
            failed("%s: %s: %s" % (name, type(exc).__name__, exc))

    # 4. fault injection (end-to-end fail-closed controls)
    for cid, name, desc in (("R.N13", "check_constants.py", "nuclear constant 192 in Proposition 3.1"),
                            ("R.N14", "check_appendix_a.py", "c_i = beta_i in the Appendix A recurrence")):
        try:
            code, so, se = run_sub(["-S", "-s", "-B", name, "--inject-fault"], "0")
            control(cid, "%s --inject-fault (%s)" % (name, desc), not is_fail(code, so))
        except Exception as exc:
            failed("%s: %s: %s" % (cid, type(exc).__name__, exc))
    try:
        code, so, se = run_sub(["-S", "-s", "-B", "-c", "print('FAIL: control'); raise SystemExit(1)"], "0")
        control("R.N4", "a subprocess that prints a FAIL line and exits with status 1",
                is_pass(code, so, se, "control") or not is_fail(code, so))
    except Exception as exc:
        failed("R.N4: %s: %s" % (type(exc).__name__, exc))

    # 5. CHECKERS.txt
    try:
        own_controls.sort(key=lambda c: int(c[0].split(".N")[1]))
        listed = parse_checkers_txt(read_file("CHECKERS.txt").decode("ascii"))
        executed["run_checks.py"] = own_controls
        mism = [k for k in list(CHECKERS) + ["run_checks.py"] if listed.get(k) != executed.get(k)]
        if mism or sorted(listed) != sorted(list(CHECKERS) + ["run_checks.py"]):
            failed("CHECKERS.txt does not match the executed negative controls: " + ", ".join(mism))
        else:
            passed("CHECKERS.txt lists exactly the %d negative controls executed and rejected"
                   % sum(len(v) for v in executed.values()))
    except Exception as exc:
        failed("CHECKERS.txt: %s: %s" % (type(exc).__name__, exc))
    for cid, desc in own_controls:
        out("  control %s rejected: %s" % (cid, desc))
    return finish()


def finish():
    if FAILED:
        out("RESULT: FAIL KE-02 exact checks (%d failure(s))" % len(FAILED))
    else:
        out("RESULT: PASS KE-02 exact checks")
    sys.stdout.write("\n".join(LINES) + "\n")
    sys.stdout.flush()
    return 1 if FAILED else 0


if __name__ == "__main__":
    try:
        code = main()
    except BaseException as exc:             # fail closed
        sys.stdout.write("\n".join(LINES) + "\nFAIL: run_checks.py: %s\nRESULT: FAIL KE-02 exact checks\n"
                         % type(exc).__name__)
        code = 1
    sys.exit(code)
