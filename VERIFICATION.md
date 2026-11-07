# Verification

Python checks use only the standard library. The exact checkers use integer
and rational arithmetic, rational square-root brackets verified by exact
squaring and exact Sturm bisection, with no floating-point tolerance. The
Lean theorem `KE02.coreCertificate` proves the finite and scalar core of the
argument; the spectral theory, the matrix statements of Section 3, the
oracle as an algorithm, the operation counts and Theorem 1.1 as a whole are
written proofs in the [paper](paper/main.pdf). The outputs below were
observed with Python 3.12 from the repository root unless stated otherwise.

## Exact checks

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

Both commands exit zero with empty standard error and identical standard
output, 132 lines, which end with

```text
PASS: CHECKERS.txt lists exactly the 70 negative controls executed and rejected
RESULT: PASS KE-02 exact checks
PASS: core/run_checks.py (normal, optimized, hash-seed)
PASS: 69 files authenticated; 6 integrity controls rejected
RESULT: PASS KE-02 exact verification
```

The standard-output SHA256 is
`184bca8b616583a08516d8de76afa74a59124ad96258759dd623a25a0c4a9afe`.

The entry point authenticates every file in `verification/`, including the
numerical illustrations and the review record, against its manifest, binds
the child runner `verification/core/run_checks.py` and its manifest by
digest, runs the child in normal, optimized and alternate hash-seed modes
with the same recorded output, and rejects six altered inventories. The
child prints, for every check family, its paper reference and its numbers of
checks and rejected negative controls, for example

```text
PASS: C12 Algorithm 2, Theorem 4.2, (37)-(40), Theorem 1.1, (5) [K, theta, Bernoulli, 2^-34]: 81188 checks, 5 negative controls rejected
PASS: A04 Appendix A pipeline, Lemma 4.3 [R >= 8n/eta, k square roots, lambda^_j = r^_{n+1-j} - 2]: 260 checks, 3 negative controls rejected
```

## The exact checkers

The child runner can be run on its own:

```sh
python3 -S -s -B verification/core/run_checks.py
python3 -S -s -B -O verification/core/run_checks.py
```

Both commands exit zero with empty standard error and identical standard
output, the first 129 lines above, ending with
`RESULT: PASS KE-02 exact checks`; the standard-output SHA256 is
`451004b7c28b3de7cbe33e5ed44147c1adea023592e637ca18b926f9abd0ea24`, the
digest recorded in `verification/run.py`. The runner verifies its manifest,
lints the checkers, and runs each checker in-process and under
`-S -s -B` and `-S -s -B -O` with two hash seeds, requiring byte-identical
output, the pinned counts and the negative controls listed in
[CHECKERS.txt](verification/core/CHECKERS.txt). The two checkers print

```text
RESULT: PASS check_constants.py: 208690 checks, 43 negative controls rejected
RESULT: PASS check_appendix_a.py: 2660 checks, 13 negative controls rejected
```

Statements that are universal in $n$ or $K$ are checked on the finite ranges
stated in the output, and statements about all matrices or functions on
fixed exact instances; see the [exact-check guide](verification/core/README.md).

## Lean formalization

The project pins Lean `v4.34.0-rc2` and Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`; the transitive dependency
revisions are pinned in [lean/lake-manifest.json](lean/lake-manifest.json).
From `lean/`, as in the [Lean guide](lean/README.md), with the toolchain's
`bin` directory first on `PATH`:

```sh
export LEAN_NUM_THREADS=4
lake exe cache get
lake build
lake env lean audit/Axioms.lean
python3 -B audit/test_verify.py
python3 -B -O audit/test_verify.py
python3 -B audit/verify.py
python3 -B -O audit/verify.py
```

**Lean build result.** The project was rebuilt from source on 2026-11-07,
with the prebuilt dependencies at the pinned revisions, under a 16 GB memory
limit and `LEAN_NUM_THREADS=4`. `lake build` reported
`Build completed successfully (3141 jobs).`, and the axiom probe printed

```text
'KE02.coreCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`audit/test_verify.py` reported `OK: 21 controls, 21 passed` in both Python
modes. `audit/verify.py` exited zero with empty standard error and printed,
identically under `-O`,

```text
PASS: 40 Lean files and 7 other files match audit/source-hashes.json
PASS: 19 statement files match audit/statement-hashes.json
PASS: no forbidden tokens or commands in any Lean file
PASS: Lean 4.34.0-rc2, Mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0
PASS: clean rebuild of 31 modules; no dependency rebuilt
PASS: 'KE02.coreCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: positive probes elaborate (audit/Probes.lean)
PASS: negative probe audit/probes/MissingAccuracy.lean fails at line 18 (Tactic `assumption` failed)
PASS: negative probe audit/probes/WrongRadius.lean fails at line 19 (Type mismatch)
PASS: negative probe audit/probes/WrongStoppingConstant.lean fails at line 7 (Type mismatch)
PASS: negative probe audit/probes/WrongTheta.lean fails at line 11 (unsolved goals)
PASS: negative probe audit/probes/WrongThreshold.lean fails at line 7 (Tactic `decide` proved that the proposition)
PASS: negative probe audit/probes/WrongTieRule.lean fails at line 7 (Type mismatch)
PASS: negative probe audit/probes/WrongWeightConstant.lean fails at line 11 (Type mismatch)
PASS: inputs unchanged during verification
PASS: all checks
```

with standard-output SHA256
`d340e1890d15516c6a2f271a1e25b3a5c2b7dc561df6eb8aa027e2b91a5900ad`. The
verifier checks every Lean file and the configuration against the pinned
source manifest, the statement files a second time against the statement
manifest, rejects proof shortcuts and unexpected commands, requires the
exact Lean version output and a clean Mathlib checkout at the pinned
revision, deletes only the package's own build directory, rebuilds every
module, fails if any dependency is rebuilt, requires exactly the three
standard axioms, elaborates the positive probes and requires every negative
probe to fail in its final example with its pinned kind of error. What the
theorem covers, with every quantifier and premise, is in
[lean/SCOPE.md](lean/SCOPE.md); see the
[section map](paper-lean-mapping/by-section.md) for the paper results it
supports.

## Paper-to-Lean correspondence map

```sh
python3 -S -s -B paper-lean-mapping/build_and_check.py
python3 -S -s -B -O paper-lean-mapping/build_and_check.py
```

Both commands exit zero with empty standard error and identical standard
output:

```text
PASS: 23 numbered results in 6 numbered sections and appendix A, in TeX order
PASS: 108 Lean fields mapped to their proofs: 82 fields of the 9 components of KE02.CoreCertificate and 26 fields of KE02.Algorithm2Outcome
PASS: 18 exact-check families, 8 supporting paper anchors and 4 numerics items
PASS: by-section.md tables and references match the mapping
PASS: coverage: 4 formalized in full, 9 formalized scalar part only, 7 exact finite cross-check only, 3 written proof only
PASS: 45 mapping negative controls rejected
RESULT: PASS mapping structure; mathematical coverage is stated per entry
```

The standard-output SHA256 is
`820d68f931384f8a5b016a51b37ba33583195dfeba30ba96d09cddf727ac6fc6`.
This checks references and the stated coverage of each entry. It does not
infer mathematical equivalence from prose and does not replace the Lean
build or the exact checks. See the [reading guide](paper-lean-mapping/README.md).

## Markdown math

```sh
python3 -I -B tools/check_markdown_math.py
python3 -I -B -O tools/check_markdown_math.py
```

The static guard checks the Markdown files of the repository against the
GitHub math profile and runs its own positive and negative controls. Both
commands give the same result:

```text
PASS: 17 Markdown files; controls passed
```

No file is exempted. The guard accepts an escaped pipe only inside a code
span on a table row, where it is GitHub's syntax for a literal pipe in a
cell.

## Manuscript

From `paper/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape -outdir=build/ci main.tex
```

This builds 28 pages with no undefined references or citations, no overfull
or underfull boxes and no BibTeX warnings; the only LaTeX warnings are four
float-placement adjustments. The included `paper/main.pdf` has SHA256
`aa1c90e6b749a98dd55859b57bb5458e9cde430ddf34c8d0472d05d54c34fec9`.
The text extracted from the included and the rebuilt PDF by
`pdftotext -layout` is identical; its SHA256 is
`8306aa23f82a58c0d38f6936874c7e7c35a0c4a27ccd25106df7a4d3a9e3b44e`.
PDF container metadata may differ between builds. See the
[paper guide](paper/README.md).

## Numerical illustrations

The code and data in [verification/numerics/](verification/numerics/README.md)
produce Section 5 of the paper. They need numpy, scipy, pandas, matplotlib
and python-flint, are not part of any proof and are not run by the commands
above; `verification/run.py` only authenticates their files. Their commands
are in the [numerics guide](verification/numerics/README.md).

## File integrity

The root manifest lists every file of the repository except itself. Run:

```sh
sha256sum --check SHA256SUMS
(cd paper && sha256sum --check SHA256SUMS)
(cd verification && sha256sum --check SHA256SUMS)
(cd verification/core && sha256sum --check SHA256SUMS)
```

The nested manifests in `paper/`, `verification/` and `verification/core/`,
and the source and statement manifests of the Lean project, bind the
manuscript, the exact checks, the numerical illustrations, the review record
and the Lean sources. Dependency caches and build products are excluded.
File hashes establish byte identity; the commands above supply the
verification evidence.
