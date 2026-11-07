#!/usr/bin/env python3
"""Fail-closed verification of the KE02 Lean core.

Checks the pinned source, statement and configuration inventory, rejects
proof shortcuts, removes the package's own build directory, rebuilds every
module, requires the exact standard axiom set for the aggregate theorem,
elaborates the positive probes and requires every negative probe to fail
inside its final example. Python standard library only; the output does not
depend on optimization flags.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
THEOREM = "KE02.coreCertificate"
EXPECTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
AXIOMS_PATH = "audit/Axioms.lean"
AXIOMS_SOURCE = (
    "import KE02\n\n"
    "example : KE02.CoreCertificate := KE02.coreCertificate\n\n"
    "#print axioms KE02.coreCertificate\n"
)
AXIOMS_OUTPUT = re.compile(
    r"'KE02\.coreCertificate' depends on axioms: \[([^\[\]\r\n]*)\]\n\Z")
POSITIVE_PROBES = "audit/Probes.lean"
NEGATIVE_PROBE_DIR = "audit/probes"
LEAN_VERSION = "4.34.0-rc2"
MATHLIB_REV = "85e3a25e006c35636f0e53b0e9296caca2685bc0"

SOURCE_HASHES_PATH = "audit/source-hashes.json"
SOURCE_HASHES_SHA256 = "f1a3ff0b6a9f1ae49a67befcc7ebc09b422895c94770789f691ed76f70da7d4a"
STATEMENT_HASHES_PATH = "audit/statement-hashes.json"
STATEMENT_HASHES_SHA256 = "fe63710db23543deef9db53697aeefc20bfeea6b42f79f7177fdb32721f6e131"
# The literal definitions and the statements of every certified result.
STATEMENT_FILES = frozenset({
    "KE02.lean",
    "KE02/Statement.lean",
    "KE02/SlopeDefinitions.lean",
    "KE02/Algorithm2Definitions.lean",
    "KE02/EndpointStatement.lean",
    "KE02/Algorithm2Statement.lean",
    "KE02/BasicSelectorDefinitions.lean",
    "KE02/BasicSelectorStatement.lean",
    "KE02/GraeffeDefinitions.lean",
    "KE02/GraeffeStatement.lean",
    "KE02/CoefficientDefinitions.lean",
    "KE02/CoefficientStatement.lean",
    "KE02/RootExtractionDefinitions.lean",
    "KE02/RootExtractionStatement.lean",
    "KE02/ContinuantDefinitions.lean",
    "KE02/ContinuantStatement.lean",
    "KE02/LocalConstantsStatement.lean",
    "KE02/WronskianStatement.lean",
    AXIOMS_PATH,
})
CONFIGURATION_FILES = frozenset({
    "lakefile.toml", "lean-toolchain", "lake-manifest.json", ".gitignore",
    "README.md", "SCOPE.md", "audit/test_verify.py",
})
REQUIRED_SOURCES = frozenset({"KE02.lean", "KE02/Statement.lean", AXIOMS_PATH, POSITIVE_PROBES})

MODULE_PATH = re.compile(r"KE02(?:/[A-Z][A-Za-z0-9]*)?\.lean\Z")
PROBE_PATH = re.compile(r"audit/probes/[A-Z][A-Za-z0-9]*\.lean\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
# Comments, strings and identifiers are all scanned.
FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|native_eval|implemented_by|extern|"
    r"opaque|ofReduceBool|ofReduceNat|elab|elab_rules|macro|macro_rules|syntax|run_tac|"
    r"run_cmd|run_elab|initialize|builtin_initialize|set_option|addDecl|debug|notation|infix|"
    r"infixl|infixr|prefix|postfix|instance|attribute|export|partial)\b")
# Any `#` command, anywhere on a line; only the fixed axiom probe may use one.
COMMAND = re.compile(r"#[A-Za-z_]")
ERROR_LINE = re.compile(
    r"^(?P<file>[^\n:]+):(?P<line>\d+):(?P<col>\d+): error: (?P<message>[^\n]*)", re.MULTILINE)
# Every negative probe and the kind of error it must produce in its final example.
NEGATIVE_PROBES = {
    "audit/probes/MissingAccuracy.lean": "Tactic `assumption` failed",
    "audit/probes/WrongRadius.lean": "Type mismatch",
    "audit/probes/WrongStoppingConstant.lean": "Type mismatch",
    "audit/probes/WrongTheta.lean": "unsolved goals",
    "audit/probes/WrongThreshold.lean": "Tactic `decide` proved that the proposition",
    "audit/probes/WrongTieRule.lean": "Type mismatch",
    "audit/probes/WrongWeightConstant.lean": "Type mismatch",
}
LEAN_VERSION_OUTPUT = ("Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit "
                       "6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)\n")


class AuditError(Exception):
    """A verification condition failed."""


def require(condition, message):
    if not condition:
        raise AuditError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_regular(root, name):
    path = Path(root) / name
    require(path.is_file(), f"Missing file: {name}")
    current = path
    while current != Path(root):
        require(not current.is_symlink(), f"Linked project file: {name}")
        current = current.parent
    return path.read_bytes()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate manifest field: {key}")
        result[key] = value
    return result


def load_manifest(raw, pin, sections):
    require(sha(raw) == pin, "Manifest does not match its SHA256 pin")
    try:
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditError("Malformed manifest") from error
    require(isinstance(value, dict) and set(value) == {"schema", *sections},
            "Unexpected manifest fields")
    require(type(value["schema"]) is int and value["schema"] == 1, "Unsupported manifest schema")
    for section in sections:
        entries = value[section]
        require(isinstance(entries, dict) and entries, f"Empty manifest section: {section}")
        for name, digest in entries.items():
            require(isinstance(name, str) and isinstance(digest, str)
                    and SHA256.fullmatch(digest) is not None, f"Invalid manifest entry: {name!r}")
    return value


def lean_kind(name):
    if MODULE_PATH.fullmatch(name):
        return "module"
    if name in (AXIOMS_PATH, POSITIVE_PROBES) or PROBE_PATH.fullmatch(name):
        return "audit"
    return None


def reject_forbidden(source, name):
    match = FORBIDDEN.search(source)
    if match is not None:
        raise AuditError(f"Disallowed token in {name}: {match.group(0)}")
    if name != AXIOMS_PATH:
        command = COMMAND.search(source)
        require(command is None, f"Disallowed command in {name}")


def source_paths(root):
    """All Lean files below the project, excluding only `.lake` and `.git`."""
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), "Invalid project directory")
    found = []

    def walk_error(error):
        raise AuditError(f"Cannot enumerate project sources: {error}")

    for current, directories, files in os.walk(root, onerror=walk_error, followlinks=False):
        current = Path(current)
        if current == root:
            directories[:] = [d for d in directories if d not in {".lake", ".git"}]
        for name in directories + files:
            require(not (current / name).is_symlink(),
                    f"Project symlink is not allowed: {(current / name).relative_to(root)}")
        for name in files:
            if name.endswith(".lean"):
                found.append((current / name).relative_to(root).as_posix())
    return sorted(found)


def check_sources(root):
    """Return the bytes of every bound file after checking the full binding."""
    root = Path(root)
    manifest = load_manifest(read_regular(root, SOURCE_HASHES_PATH), SOURCE_HASHES_SHA256,
                             ("sources", "configuration"))
    sources, configuration = manifest["sources"], manifest["configuration"]
    require(set(configuration) == CONFIGURATION_FILES, "Configuration inventory differs")
    for name in sources:
        require(lean_kind(name) is not None, f"Invalid bound source path: {name}")
    require(REQUIRED_SOURCES <= set(sources), "Required source missing from the binding")
    actual = source_paths(root)
    require(set(actual) == set(sources),
            "Lean source inventory differs from its binding: "
            f"missing {sorted(set(sources) - set(actual))}; "
            f"extra {sorted(set(actual) - set(sources))}")
    snapshot = {SOURCE_HASHES_PATH: read_regular(root, SOURCE_HASHES_PATH)}
    for name, digest in sorted({**sources, **configuration}.items()):
        data = read_regular(root, name)
        require(sha(data) == digest, f"Bound file changed: {name}")
        if name.endswith(".lean"):
            try:
                text = data.decode("utf-8")
            except UnicodeDecodeError as error:
                raise AuditError(f"Lean source is not UTF-8: {name}") from error
            reject_forbidden(text, name)
        snapshot[name] = data
    require(snapshot[AXIOMS_PATH] == AXIOMS_SOURCE.encode("utf-8"), "The axiom probe changed")
    return snapshot


def check_statements(root, snapshot):
    """The statement files are bound a second time, by their own manifest."""
    raw = read_regular(root, STATEMENT_HASHES_PATH)
    manifest = load_manifest(raw, STATEMENT_HASHES_SHA256, ("statements",))
    statements = manifest["statements"]
    require(set(statements) == STATEMENT_FILES, "Statement inventory differs")
    for name, digest in statements.items():
        require(name in snapshot, f"Statement file is not a bound source: {name}")
        require(sha(snapshot[name]) == digest, f"Statement file changed: {name}")
    check_statement_closure(snapshot)
    snapshot = dict(snapshot)
    snapshot[STATEMENT_HASHES_PATH] = raw
    return snapshot


def local_imports(source):
    """The `KE02` modules imported by a Lean source."""
    found = []
    for line in source.splitlines():
        match = re.match(r"\s*import\s+(.+)", line)
        if match:
            for dependency in match.group(1).split("--", 1)[0].split():
                if dependency == "KE02" or dependency.startswith("KE02."):
                    found.append(dependency)
    return found


def local_import_closure(snapshot, root_module):
    """`root_module` and every local module it imports, directly or not."""
    sources = {name[:-5].replace("/", "."): data.decode("utf-8")
               for name, data in snapshot.items() if MODULE_PATH.fullmatch(name)}
    closure, pending = set(), [root_module]
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        require(module in sources, f"Missing local import: {module}")
        closure.add(module)
        pending.extend(local_imports(sources[module]))
    return sorted(closure)


def check_statement_closure(snapshot):
    """Everything `KE02.Statement` depends on locally is itself a statement file."""
    for module in local_import_closure(snapshot, "KE02.Statement"):
        require(module.replace(".", "/") + ".lean" in STATEMENT_FILES,
                f"The statement imports a module outside the statement files: {module}")


def module_order(snapshot):
    """Local modules, dependencies first; every module must be reachable from `KE02`."""
    sources = {name[:-5].replace("/", "."): data.decode("utf-8")
               for name, data in snapshot.items() if MODULE_PATH.fullmatch(name)}
    visited, visiting, ordered = set(), set(), []

    def visit(module):
        require(module in sources, f"Missing local import: {module}")
        require(module not in visiting, f"Local import cycle: {module}")
        if module in visited:
            return
        visiting.add(module)
        for dependency in local_imports(sources[module]):
            visit(dependency)
        visiting.remove(module)
        visited.add(module)
        ordered.append(module)

    require("KE02" in sources, "Missing root module KE02")
    visit("KE02")
    unreachable = sorted(set(sources) - visited)
    require(not unreachable, f"Modules not imported by KE02: {unreachable}")
    return ordered


def parse_axioms(stdout, stderr=""):
    require(not stderr, "Unexpected standard error from the axiom check")
    match = AXIOMS_OUTPUT.fullmatch(stdout)
    if match is None:
        raise AuditError("Missing, malformed, or additional axiom output: expected exactly "
                         f"one line \"'{THEOREM}' depends on axioms: [...]\"")
    names = [name.strip() for name in match.group(1).split(",")]
    require(len(names) == len(EXPECTED_AXIOMS) and set(names) == EXPECTED_AXIOMS,
            f"Unexpected axiom list: {names}")
    return names


def last_example_line(source):
    lines = [index + 1 for index, line in enumerate(source.splitlines())
             if line.startswith("example")]
    require(len(lines) >= 2, "A negative probe needs a passing and a failing example")
    return lines[-1]


def classify_negative(name, source, returncode, output, expected):
    """A negative probe must fail only inside its final example, with the
    pinned kind of error."""
    require(returncode != 0, f"Negative probe elaborated: {name}")
    errors = [(int(m.group("line")), m.group("message")) for m in ERROR_LINE.finditer(output)]
    require(errors, f"Negative probe failed without a Lean error: {name}")
    first = last_example_line(source)
    require(all(line >= first for line, _ in errors),
            f"Negative probe failed before its final example: {name}")
    require(any(message.startswith(expected) for _, message in errors),
            f"Negative probe failed with an unexpected error kind: {name}")
    return min(line for line, _ in errors)


def check_build_output(output):
    """Only project modules may be compiled; the dependency cache is read only."""
    for line in output.splitlines():
        match = re.search(r"\bBuilt\s+([A-Za-z0-9_.]+)", line)
        if match:
            module = match.group(1)
            require(module == "KE02" or module.startswith("KE02."),
                    f"A dependency was rebuilt: {module}")


def run_checked(command, root, expect_success=True):
    try:
        result = subprocess.run(command, cwd=root, text=True, encoding="utf-8",
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    except (OSError, UnicodeError) as error:
        raise AuditError(f"Could not execute {command[0]}: {error}") from error
    if expect_success and result.returncode != 0:
        sys.stderr.write(result.stdout[-4000:] + result.stderr[-4000:])
        raise AuditError(f"Command failed with status {result.returncode}: {' '.join(command)}")
    return result


def clean_build_directory(root):
    """Remove only this package's own build products."""
    root = Path(root)
    lake_dir = root / ".lake"
    require(lake_dir.is_dir() and not lake_dir.is_symlink(), "Missing or linked .lake directory")
    build = lake_dir / "build"
    if build.exists() or build.is_symlink():
        require(not build.is_symlink() and build.is_dir(), "The build directory is linked")
        require(build.resolve().parent == lake_dir.resolve(), "Unexpected build directory")
        shutil.rmtree(build)
    require(not build.exists(), "The build directory could not be removed")


def check_toolchain(root):
    lake = shutil.which("lake")
    require(lake is not None, "lake is not on PATH")
    version = run_checked([lake, "env", "lean", "--version"], root)
    check_lean_version(version.stdout, version.stderr)
    manifest = json.loads(read_regular(root, "lake-manifest.json").decode("utf-8"))
    revisions = {entry["name"]: entry["rev"] for entry in manifest["packages"]}
    require(revisions.get("mathlib") == MATHLIB_REV, "Mathlib revision differs in the manifest")
    mathlib = Path(root) / ".lake" / "packages" / "mathlib"
    head = run_checked(["git", "-C", str(mathlib), "rev-parse", "HEAD"], root).stdout.strip()
    require(head == MATHLIB_REV, "Installed Mathlib revision differs")
    status = run_checked(["git", "-C", str(mathlib), "status", "--porcelain"], root)
    check_clean_checkout(status.stdout, status.stderr)
    return lake


def check_lean_version(stdout, stderr=""):
    require(not stderr and stdout == LEAN_VERSION_OUTPUT, "Lean version output differs")


def check_clean_checkout(stdout, stderr=""):
    require(not stderr and stdout == "", "The Mathlib checkout is not clean")


def verify(root=ROOT):
    root = Path(root)
    before = check_statements(root, check_sources(root))
    modules = module_order(before)
    lean_files = [name for name in before if name.endswith(".lean")]
    print(f"PASS: {len(lean_files)} Lean files and {len(CONFIGURATION_FILES)} other files "
          f"match {SOURCE_HASHES_PATH}")
    print(f"PASS: {len(STATEMENT_FILES)} statement files match {STATEMENT_HASHES_PATH}")
    print("PASS: no forbidden tokens or commands in any Lean file")
    lake = check_toolchain(root)
    print(f"PASS: Lean {LEAN_VERSION}, Mathlib {MATHLIB_REV}")
    clean_build_directory(root)
    build = run_checked([lake, "build", *modules], root)
    check_build_output(build.stdout + build.stderr)
    for module in modules:
        olean = root / ".lake" / "build" / "lib" / "lean" / (module.replace(".", "/") + ".olean")
        require(olean.is_file(), f"Module was not built: {module}")
    print(f"PASS: clean rebuild of {len(modules)} modules; no dependency rebuilt")
    result = run_checked([lake, "env", "lean", AXIOMS_PATH], root)
    names = parse_axioms(result.stdout, result.stderr)
    print(f"PASS: '{THEOREM}' depends on axioms: [{', '.join(names)}]")
    probes = run_checked([lake, "env", "lean", POSITIVE_PROBES], root)
    require(ERROR_LINE.search(probes.stdout + probes.stderr) is None, "Positive probe error")
    print(f"PASS: positive probes elaborate ({POSITIVE_PROBES})")
    negatives = sorted(name for name in before if PROBE_PATH.fullmatch(name))
    require(negatives == sorted(NEGATIVE_PROBES), "Negative probe inventory differs")
    for name in negatives:
        result = run_checked([lake, "env", "lean", name], root, expect_success=False)
        line = classify_negative(name, before[name].decode("utf-8"), result.returncode,
                                 result.stdout + result.stderr, NEGATIVE_PROBES[name])
        print(f"PASS: negative probe {name} fails at line {line} ({NEGATIVE_PROBES[name]})")
    require(check_statements(root, check_sources(root)) == before,
            "Sources changed during verification")
    print("PASS: inputs unchanged during verification")
    print("PASS: all checks")


def main():
    try:
        verify()
    except (AuditError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
