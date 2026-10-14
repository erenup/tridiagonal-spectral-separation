# Exact supporting checks

Run the complete Python suite from the repository root:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

Python 3.11 or later and its standard library are sufficient. The two commands
produce identical output. Every condition is checked by explicit failure
branches that remain active under `-O`.

The [exact-real checks](exact-real/verification/README.md) use integers and
rational arithmetic to check polynomial identities, coefficient ratios,
convex selection, inverse tunnelling identities, and constants on finite
families. The [finite-precision checks](finite-precision/verification/README.md)
regenerate eleven exact certificates and test the independent verifier.
The [paper constants checker](../paper/check_constants.py) checks the numerical
constants used in the paper. None of these finite computations establishes
the all-input theorem or the asymptotic complexity statements.

The complete suite executes the mathematical checks in normal, optimized, and
alternate-hash-seed modes. It checks 57 exact-real, 156 finite-precision, and
9 paper-constant reason-specific rejection runs. The corresponding inventories
contain 19, 27, and 3 distinct mathematical controls. Six exact-real and nine
finite-precision integrity controls test file coverage, hashes, and required
checks. Eleven further entrypoint controls test altered or missing children,
incomplete or duplicated manifests, changed checker bindings, nonzero exit
status, standard error, and incorrect output.

The entrypoint verifies [SHA256SUMS](SHA256SUMS), the exact file inventory,
the child runner and its manifest, and the paper constants checker before
execution. The child runners authenticate their proof documents, code,
fixtures, certificates, control lists, and expected output hashes. All
inventories are checked again after execution. Symbolic links and unregistered
files are rejected.

Temporary copies used by the finite-precision checks reside under
`tmp/verification/` within the finite-precision directory and are removed on
completion. No network,
external library, numerical eigensolver, or floating-point arithmetic is used.
The construction's finite-bit word bound applies to its fixed-grid integer
algorithm; the independent rational verifier has no asserted bounded-word
cost. Near-linear bit complexity remains open.

See [VERIFICATION.md](../VERIFICATION.md) for the complete expected output.
