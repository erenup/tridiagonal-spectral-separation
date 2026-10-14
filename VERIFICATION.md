# Verification

The Python checks use only the standard library and exact integer or rational
arithmetic. Run from the repository root with Python 3.11 or later:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

Both commands exit zero, have empty standard error, and produce the following
identical standard output:

```text
PASS: check_convex_selector.py (normal, optimized, hash-seed)
PASS: check_inverse_tunneling.py (normal, optimized, hash-seed)
PASS: check_primitives.py (normal, optimized, hash-seed)
PASS: check_recursive_primitives.py (normal, optimized, hash-seed)
PASS: 57 negative-control runs; 2 proof bindings
PASS: 6 integrity controls rejected
PASS: 11 fixtures regenerated and verified in normal, optimized and hash-seed modes
PASS: 156 reason-specific negative-control runs; all 27 cases receive each selected mode
PASS: 9 inertia and 3 safeguarded cases per mode
PASS: 4401-digit fresh-loader checks; 2 proof bindings; immutable source inventory
PASS: 9 runner integrity controls rejected
RESULT: PASS KE-02 finite-precision verification
RESULT: PASS KE-02 verification
PASS: paper constants in normal, optimized and hash-seed modes
PASS: 9 reason-specific paper negative-control runs
PASS: 11 entrypoint integrity controls rejected
RESULT: PASS tridiagonal spectral separation verification
```

The standard-output SHA256 is
`7ddb78b7186b3a1d397584fe71091fb813a45c25967ef5f39fc1a56b905325d7`.

There are 222 reason-specific mathematical rejection runs per command:
57 exact-real, 156 finite-precision, and 9 paper-constant runs. These cover
19, 27, and 3 distinct corruption cases, respectively. The finite-precision
count includes both isolated harness executions and direct repetitions that
receive the selected hash seed. There are also 26 in-memory integrity
controls: 6 exact-real, 9 finite-precision, and 11 entrypoint controls.

File and output authentication remain active under optimization. The
entrypoint rejects missing or additional files, symlinks, incomplete or
duplicated manifests, altered code, changed paper-checker bindings, nonzero
child status, standard error, and unexpected output. The nested suites check
proof bindings and their complete required control inventories. See the
[verification guide](verification/README.md) for the file layout and scope.

## Lean core

After installing the pinned Lean toolchain and obtaining the dependencies
as described in [lean/README.md](lean/README.md), run:

```sh
python3 -B lean/verify.py
```

The verified build compiled all 18 production modules into initially empty
objects and obtained exactly:

```text
'KE02.coreCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: 18 modules freshly compiled; exact standard axiom set.
```

The verifier also authenticates source/configuration inventories, the compiler
version and binary, nine dependency revisions, and dependency object hashes
before and after compilation. The installed toolchain and official dependency
cache are trusted inputs; those objects are not independently rebuilt.

The finite arithmetic checks and verifier controls can be run from `lean/`:

```sh
python3 -B audit/test_exact.py
python3 -B audit/test_verify.py
python3 -O -B audit/test_exact.py
python3 -O -B audit/test_verify.py
```

All four commands pass: 8 exact-checker tests and 66 verifier-control tests
in each mode. Exact checker child outputs and statuses agree byte for byte
between normal and optimized modes. The unittest diagnostic text agrees
except for elapsed time. The controls cover malformed data, altered
coefficients, invalid root hypotheses, invalid approximate replies, changed
source and configuration, forbidden proof constructs, dependency problems,
invalid axiom output, failed processes, and changes during compilation.

The formal theorem proves the robust scalar selector contract, universal
Graeffe identities, and positive ordered-root coefficient/ratio bounds. It
does not formalize the Hermitian spectral bridge, inverse tunnelling,
quasimode argument, eigenvalue oracle, complete matrix algorithm, or either
complexity theorem. The finite computations check examples and constants;
the universal spectral and complexity claims are established in the paper.

## Paper-to-check mapping

Run from the repository root:

```sh
python3 -B paper-lean-mapping/build_and_check.py
python3 -O -B paper-lean-mapping/build_and_check.py
```

Both commands exit zero with empty standard error and identical output:

```text
PASS: 13 numbered paper results, 3 polynomial ingredients; labels, declarations, exact-check paths and section table; 13 rejection controls
```

The standard-output SHA256 is
`e73266fe51c61fc8a043b160ac2a2f6efd922fc14e80600d7cb4f060ad63b1e5`.
The map covers all 13 numbered results and all 102 source labels. The
checker validates the stated Lean declarations and exact-program paths,
and checks the generated section table. Its 13 rejection controls run
in both modes. Seven additional malformed-package cases were rejected
in separate processes in both modes, for 14 process-level rejection runs.
The map checks references and scope records; it does not replace the
Lean build, mathematical checks or written proofs.

## Manuscript build

From `paper/`, with a TeX installation providing the packages in `main.tex`:

```sh
SOURCE_DATE_EPOCH=1791937820 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build main.tex
```

The build produced 21 pages with no unresolved references or citations
and no overfull boxes. The included `paper/main.pdf` is that output;
its SHA256 is
`93240b4b284b46e0e9757e5c57bcb1c590dcf6ce9b7ca9a5132c22a05025fadb`.
The PDF records the title and author placeholder `TBD`. The constant
checker in `paper/` is included in the exact verification entry point.

## File integrity

The root manifest lists every included file except itself. From the
repository root, check the file bytes with:

```sh
sha256sum --check SHA256SUMS
```

The nested manifests bind the files used by the exact suites and paper.
Build products and downloaded dependencies are excluded from the root
manifest and must be obtained as described in the Lean guide. A matching
file hash establishes identity, not mathematical correctness.
