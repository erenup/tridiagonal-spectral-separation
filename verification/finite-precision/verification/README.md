# Finite-precision construction and exact verification

Run the complete standard-library suite from the finite-precision folder:

```sh
python3 -S -s -B verification/run.py
```

The mathematical claims and their quantifiers are in
[the statement](../proofs/STATEMENT.md) and [the proof](../proofs/PROOF.md).
The construction uses integers, and the independent certificate verifier uses
integers and exact rational arithmetic. The verifier does not import the
constructor. Neither program uses a numerical eigensolver or floating-point
arithmetic.

## Input and certificate

An input has exactly the following fields:

```json
{
  "schema": "KE02.input.v1",
  "n": 2,
  "d": 2,
  "diagonal": [0, 0],
  "edge_real": [0],
  "edge_imag": [0]
}
```

Every numerical field is an integer; booleans are rejected. The theorem
requires n ≥ 2 and d ≥ 2. The array lengths are n, n−1, n−1. Their entries
are numerators over the common denominator Q=2^p, where p is determined by
the theorem's formulas. An off-diagonal entry uses its listed real and
imaginary parts, with the conjugate in the opposite triangle. The component
enclosure radius is 1/Q, and the perturbation budget is δ=2^−d.

The constructor writes the scalar center c, the diagonal D=c diag(1,…,n),
the parameter values, three lists of ordered-eigenvalue brackets, and an
upper bound for the convexity defect. Center, diagonal and bracket numerators
use denominator Q. The verifier independently recomputes the parameters and
defect rather than trusting their advertised values.

The verifier requires the intended input separately from the certificate and
rejects disagreement with its embedded input. A passing certificate establishes
the written gap consequence uniformly for every normalized complex Hermitian
tridiagonal matrix in that input's component enclosure. It does not establish
that such a matrix exists. The exact necessary check ‖T₀‖ ≤ 1+5/Q does not
replace the normalization and enclosure premise.

The constructor uses signed floor division, including at negative
denominators. Its input checks include the necessary component bounds.
The verifier uses exact rational inertia with nonzero scalar pivots, isolated
zero pivots, and two-by-two pivots at a zero diagonal with a nonzero adjacent
edge. This covers zero edges, repeated eigenvalues, and endpoint equalities.
The lower spectral endpoint is inclusive and the upper endpoint is strict.

Both programs reject malformed JSON, duplicate and unknown fields, noninteger
number tokens, and booleans in integer positions. Failures use explicit
SystemExit branches, with no assertions. Their decimal conversion limit is
disabled so that large integer precision has no extra implementation cutoff.

## Reproducibility and controls

SHA256SUMS covers every file in this directory except itself. The runner
rejects missing or extra files, symlinks, cache files, nonstandard imports,
assertions and inexact numerical literals. It checks the three implementation
source hashes and the source-to-proof bindings in SOURCE_BINDINGS.txt.
OUTPUT_HASHES.json registers all deterministic generator and verifier outputs,
the complete harness report, the exact rejection messages for all 25 harness
corruptions, and the additional-control output.

The runner executes normal, optimized (-O), and second-hash-seed modes.
Each mode regenerates and verifies eleven fixtures and compares every
certificate with the stored bytes. Direct generator and verifier processes
receive the selected hash seed. The fixture harness also runs in
each mode; its isolated children propagate the optimization flag. Full
reports and outputs must agree byte for byte across all three modes and with
their registered hashes.

The fixture harness launches isolated children, which ignore environment
hash-seed settings. The runner therefore also replays each of its 25 corruption
files directly with the selected seed and checks the complete registered
rejection message. Together with the two additional cases, every corruption
receives each chosen mode. Counting the fixture harness runs and the direct
replays, the suite checks 156 reason-specific rejections.

The harness regenerates fixtures and certificates, so it runs only inside
fresh disposable copies under tmp/verification/ inside the finite-precision folder.
Generated reports, statistics and mutated controls stay in those copies.
The copied source bytes must remain identical after regeneration. The
committed verification and proof inventories are checked before and after the
suite. Scratch copies are deleted on completion, including ordinary failures.

The eleven fixtures have orders 2, 3, 4 and 8 and cover complex edges, repeated
entries, zero and weak edges, large real couplings, and a rounded nondyadic
rational matrix. fixtures/SOURCES.json records the rational source matrices.
Their normalization and proxy enclosure are checked exactly. Nine inertia
cases and three safeguarded-count cases exercise arithmetic branches. Fresh
generator and verifier processes also load and serialize a 4401-digit integer.

NEGATIVE_CONTROLS.json requires all 25 harness corruptions and two additional
corruptions in every mode. Each must reach its stated verifier failure branch.
The harness includes a center with a genuine large defect and valid spectral
enclosures. The additional cases remove a complex imaginary edge consistently
from both input bindings, and move the center to zero while preserving D=cX
and the perturbation budget. They must fail spectral enclosure and center-range
checks respectively. Runner controls separately reject altered implementation
bytes, missing and extra files, duplicate or incomplete manifests, weakened
control coverage, missing output registrations, and changed proof source
bindings, including cases with recomputed file manifests.

The finite fixture corpus and observed word lengths corroborate the programs.
The all-input runtime, word-size, certificate-size and uniform-gap bounds are
proved in the written proof. No bounded-word cost is asserted for the rational
certificate verifier. The near-linear finite-bit oracle and IE-07 remain open.
