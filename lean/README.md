# Scalar selector and polynomial core in Lean

`KE02.coreCertificate : KE02.CoreCertificate` proves the robust scalar
selector contract, universal even/odd Graeffe identities, and positive
ordered-root coefficient bounds used in the [paper](../paper/main.pdf).
Definitions use ordinary real functions, finite transcripts and polynomial
operations. The selector uses the actual approximate replies and chooses
the left child when the estimates are equal.

The [scope](FEASIBILITY_SCOPE.md) gives the exact quantifiers and exclusions;
the aggregate proposition is in [KE02/Statement.lean](KE02/Statement.lean).
The selector certificate includes the least threshold, nested query
intervals, tolerances, all-prefix potential bounds, exactly `8K` recorded
calls, and the final radius and convexity-defect estimates. The polynomial
identities cover empty root lists and arbitrary real roots. Positivity and
ordering are required only by the stated coefficient and ratio inequalities.

This is a formalization of the scalar and polynomial core. The Hermitian
spectral, quasimode, matrix-gap and arithmetic-complexity bridges remain in
the written proof. The ratio-root analytic accuracy extension is outside
this target. **No spectral value oracle implementation, or proof that one
supplies replies satisfying the selector's error premise, is formalized.**
The exact query count counts requests in the defined transcript; it does
not certify the cost of answering them or the full matrix algorithm.

## Build and verify

The audit supports Linux x86_64 with Python 3.11 or later and
elan and Lake available on `PATH`.
It pins Lean `v4.34.0-rc2` (commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`) and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The exact dependency revisions
are recorded in `lake-manifest.json`. Run from this directory:

```sh
lake exe cache get
python3 -B audit/test_exact.py
python3 -B audit/test_verify.py
python3 -O -B audit/test_exact.py
python3 -O -B audit/test_verify.py
python3 -B verify.py
```

From the repository root, the verification command is
`python3 -B lean/verify.py`. The first command above downloads the official
dependency cache. The verifier
uses `.audit-build` by default and requires a new, nonexistent output directory
each time; choose a different `--output` path for a later run. It resolves the compiler through Lake and
checks its Linux x86_64 binary digest and exact version/commit. Every one of
the 18 production modules is compiled with one thread and a 12 GiB compiler
limit into initially empty project objects. Allow at least 12 GiB of memory.

Only the new project objects and pinned dependency libraries are imported.
The verifier checks all nine dependency revisions and tracked source
cleanliness, and hashes every dependency library artifact and installed
toolchain library before and after the build. It binds the complete Lean
source/configuration/helper inventory and requires exactly `propext`,
`Classical.choice`, and `Quot.sound` for the fully typed aggregate theorem.
Missing or changed inputs, forbidden proof shortcuts, failed processes,
malformed axiom output and changed dependencies cause a nonzero exit.

The installed toolchain and downloaded official dependency cache are trusted
inputs. Their revision, binary and before/after checks do not rebuild or
independently establish the original provenance of the dependency objects.
No preexisting local theorem object is a proof input. The resulting output
directory contains compiler logs, dependency hashes and a build receipt.

The Python rational suite is a finite semantic cross-check, with negative
controls and identical normal/optimized behavior. The universal mathematical
claims come from the kernel-checked Lean theorem, not this finite suite.
