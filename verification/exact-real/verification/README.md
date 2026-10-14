# Exact supporting checks

Run `python3 -S -s -B run.py` from
this directory with Python 3.11 or later. Only the standard library is
needed. The decisive arithmetic uses integers and `fractions.Fraction`.

The [written proof](../proofs/PROOF.md) establishes the all-input
deterministic construction and its exact-operation bound. These finite
checks support its identities, signs, error handling and constants;
they do not prove the quantified theorem or its asymptotic complexity.
They do not run the complete high-precision algorithm at large dimension
and provide no bit-complexity or finite-precision guarantee.

## Checked ingredients

- `check_primitives.py` compares three continuants with permutation
  determinants, checks five positive-root families including repeated
  roots, 30 Graeffe transforms, 35 coefficient-ratio rounds, rational
  outward root intervals, and the final exponent and constants.
- `check_convex_selector.py` checks 90 rational convex piecewise-linear
  functions and 8,064 bounded-error value calls. It checks secants
  against derivative integrals, the two-child potential sum, approximate
  choices, recurrence, radius and centered defect. The fixed integer
  fixture sequence uses `random.Random(20261012).randrange`; every
  subsequent calculation is exact. These fixtures provide no stochastic
  proof support. The runner permits only this fixed integer generator
  and its two specified integer ranges.
- `check_recursive_primitives.py` separately checks Graeffe and ratio
  identities, exact difference counting, interval selection and prefix
  evaluation. It also checks supplementary normalized characteristic
  identities; these are not premises of the final construction.
- `check_inverse_tunneling.py` checks nine rational eigenpair cases,
  Wronskian and direction-projector identities, the skipped-row residual,
  both full truncation boundary entries, flattening, residual norms,
  the spectral-weight swap, and the constant comparisons.

## Negative controls and execution

Each checker includes corruption tests and exposes
four, four, four or seven corruptions through `--negative-control`.
The 19 named controls alter a sign, coefficient, choice, error promise,
radius, convexity condition, residual term, boundary contribution, weight
swap or constant. [NEGATIVE_CONTROLS.json](NEGATIVE_CONTROLS.json) lists
their exact expected errors. Every external control must exit with
status 1, empty stdout and exactly its registered stderr.

[CHECKERS.txt](CHECKERS.txt) records the expected stdout SHA256 of each
positive checker. The runner executes all four checkers and all controls
in three modes: normal with hash seed 1, `-O` with seed 1, and normal with
seed 8675309. Positive runs must exit zero, produce no stderr and match
the registered output byte for byte in every mode. There are 12 positive
executions and 57 external negative-control executions per runner call.
Site initialization and bytecode writes are disabled.

Six further in-memory controls require rejection of altered content,
an omitted checker, a duplicate manifest entry, an unregistered file,
a missing negative control, and an additional random from-import, even
after updating the corresponding manifest hashes.
All failure checks remain active under Python `-O`.

## File and proof bindings

[SHA256SUMS](SHA256SUMS) covers every verification file except itself.
The runner requires the exact file, checker and negative-control
inventories; it rejects symbolic links, bytecode files, altered hashes,
assertions, inexact literals, nonstandard imports and unsupported dynamic
calls. JSON must have unique keys and integer numbers. Except for the
fixed integer fixture generator described above, inexact random APIs
are excluded.

[SOURCE_BINDINGS.txt](SOURCE_BINDINGS.txt) gives the reference and document
hashes of `PROOF.md` and `STATEMENT.md`. The runner checks the source hash
identifiers and the exact two-file proof inventory against the document
hashes. All verification and proof hashes are checked again after the
executions. Any failed condition exits nonzero.

The finite-precision child runner is authenticated by its source SHA256 before
and after execution. Its complete stdout must match the registered SHA256;
nonzero exit status, stderr, missing files and changed source all reject.
