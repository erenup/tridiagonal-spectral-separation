# Exact verification

Run from the repository root with Python 3.11 or later:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

[run.py](run.py) is the single entry point. It authenticates every file in
this directory, including `numerics/` and `reviews/`, against
[SHA256SUMS](SHA256SUMS), binds the child runner `core/run_checks.py` and its
manifest `core/SHA256SUMS` by digest, runs the child in normal, optimized
and alternate hash-seed modes with a clean environment, requires exit status
zero, empty standard error and the recorded standard output in every mode,
and rejects six altered inventories.

- [core/](core/README.md): exact, standard-library checks of the constants
  and inequality chains of Sections 2 to 4 (Lemma 2.1 through Theorem 4.2
  and Lemma 4.3), of both algorithms run as transcripts on exact instances,
  and of the algebra of Appendix A, with integer and rational arithmetic and
  70 registered negative controls. Its runner `run_checks.py` authenticates
  the folder, lints the checkers and runs each of them five times.
- [numerics/](numerics/README.md): the code and data of the numerical
  illustrations of Section 5. They need numpy, scipy, pandas, matplotlib and
  python-flint, are not part of any proof and are not run by `run.py`, which
  only authenticates their files.
- [reviews/](reviews/README.md): the review record.

These finite checks support the written proofs; they do not replace any
statement for all matrices or all parameters. The Lean formalization is in
[lean/](../lean/README.md), and the map from each numbered result of the
paper to its evidence is [by-section.md](../paper-lean-mapping/by-section.md).
