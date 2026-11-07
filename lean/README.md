# Lean formalization of the finite and scalar core

This directory formalizes, in Lean 4 with Mathlib, the finite and scalar
core of *A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal
Matrices* (Wenqi Zhu and Ping Nie). Result, equation and page numbers refer to
[paper/main.pdf](../paper/main.pdf) (28 pages).

The aggregate theorem is

```lean
theorem KE02.coreCertificate : KE02.CoreCertificate
```

with the proposition `KE02.CoreCertificate` in
[KE02/Statement.lean](KE02/Statement.lean). It has no hypotheses: every
component is a universally quantified statement with all premises explicit.
Its kernel dependencies are exactly `propext`, `Classical.choice` and
`Quot.sound`. The exact quantifiers, the premises taken from the paper, and
everything that is not formalized are listed in [SCOPE.md](SCOPE.md).

## What is proved

| Paper | Page | Field of `CoreCertificate` | Statement file |
|---|---|---|---|
| Theorem 1.1, scalar parts: `t ∈ [0, δ/n]` and `nt ≤ δ`; at most `3 + 8K` oracle calls, all at points of `[0, δ/n]` with accuracies `δ/(2¹⁶Kn⁴) < ε < 1` for `δ < 1/2`, i.e. (40) and `ε < 1`; `K` found by doubling; the bound `h²/(2²⁰n⁴) > 2⁻³⁴δ²n⁻¹²` that Proposition 3.1 turns into the gap bound; the second inequality of (5) | 2, 20 | `algorithm2` | `Algorithm2Statement.lean` |
| (13) and (33) are nonnegative for convex `F`; (34) for `0 < θ ≤ 1/2` | 6, 16–17 | `endpoint` | `EndpointStatement.lean` |
| Lemma 4.2 for every `0 < θ ≤ 1/4`: candidate windows, (35), error `1/64` from tolerance `2θh'/256`, ties to the left, (36) for one refinement | 17 | `endpoint` | `EndpointStatement.lean` |
| Algorithm 2 and Theorem 4.2 without Proposition 3.1: `K` (least with `2^K ≥ 16n³`, found by doubling, `= ⌈log₂(16n³)⌉`), `θ = 1/(4K)`, `(1 - 1/(2K))^K ≥ 1/2`, `L_K > δ/(64n⁴)`, `1/8 + 1/128 + 1/64 < 1/2`, and the actual transcript on arbitrary replies: termination within `K` refinements, (36) along the run, windows and evaluation points in `[0, δ/n]`, (37), `h ≤ δ/(2n) < 1`, `3 + 8j ≤ 3 + 8K` requests (seven shared points and one midpoint per refinement), `h²/(2²⁰n⁴) > 2⁻³⁴δ²n⁻¹²` as used for (38), and (40) | 17–20 | `algorithm2` | `Algorithm2Statement.lean` |
| Lemma 4.1: the weight inequality and its sharpness; (29) for convex `F`; (30) for one refinement of Algorithm 1; Theorem 4.1 constants (`K_b`, `(2/3)^(K_b) n³ ≤ 1/16`, the iteration, `5/32 + 2/64 < 1/2`, the arithmetic facts `3+5j ≤ 3+5K_b` (j ≤ K_b) and `(δ/(2n))4^(−j) ≤ δ/(2n) < 1` (the evaluation count of Algorithm 1 is not formalized)); Remark 4.1, (32) | 14–16 | `basicSelector` | `BasicSelectorStatement.lean` |
| Appendix A: even/odd split, one Graeffe step and its iterates give `∏(X + r_i^(2^k))` | 27 | `graeffe` | `GraeffeStatement.lean` |
| Appendix A: `p_j ≤ e_j ≤ 2ⁿ p_j` and the ratio bounds | 27 | `coefficients` | `CoefficientStatement.lean` |
| Appendix A: (43), the `R`-th root as `k` square roots, `2^x - 1 ≤ x`, `\|r̂_j - r_j\| ≤ 4n/R ≤ η/2`, `k` least with `Rη ≥ 8n` and found by doubling `R` from `1`, `η = ε/Σj`, `λ̂_j = r̂_(n+1-j) - 2` matched index by index with error `≤ (n(n+1)/2)(η/2) ≤ ε`; Section 4.3, the remark after Lemma 4.3: the bound `n(n+1)η/2` (Lemma 4.3 itself is not formalized) | 19, 27 | `rootExtraction` | `RootExtractionStatement.lean` |
| Appendix A: the determinant of a tridiagonal matrix over any commutative ring `R : Type` is the continuant, and for every real tridiagonal `A` the recurrence `P_0 = 1`, `P_1 = z + 2 + a_1`, `P_i = (z + 2 + a_i)P_(i-1) - c_(i-1)P_(i-2)` (`2 ≤ i ≤ n`) ends in `det(zI + 2I + A)`; `c_i = A_(i,i+1)²` for symmetric `A` | 27 | `continuant` | `ContinuantStatement.lean` |
| Lemma 3.1 (scalar steps), Lemma 3.2 (`96`), Proposition 3.1 (`3/8`, `5/8 > 1/2`, the transfer inequality from (28), the chain), the chain ending in `2⁻³⁴` | 9–13, 19 | `localConstants` | `LocalConstantsStatement.lean` |
| (22), the discrete Wronskian identity for the three-term recurrence; Step 2 bounds `\|Σ_(j≤i) (u₁)_j (u₂)_j\| ≤ 1/2` and `\|β_i\| \|det(r_i, r_(i+1))\| ≤ γ/2` | 10 | `wronskian` | `WronskianStatement.lean` |

Not formalized from Theorem 1.1: the matrix conclusions `‖D‖₂ ≤ δ` and the
gap bound (which need Proposition 3.1 and spectral theory), the oracle of
Lemma 4.3, the model of computation, and every operation count, including
`O(n[1+log(n/δ)]³)`. See [SCOPE.md](SCOPE.md). Lemma 2.1 is not formalized:
convexity of F and the secant bounds (9) are premises; Lemmas 3.1–3.2 and
Proposition 3.1 enter only through scalar steps.

All statement files are in [KE02/](KE02/). The proofs are in the files
ending in `Proof`, `Universal`, `Split`, `Expansion`, `Bounds` and `Ratios`.
The main proof terms are `KE02.endpointCertificate`,
`KE02.algorithm2Certificate` (with `KE02.algorithm2_outcome` for the run),
`KE02.basicSelectorCertificate`, `KE02.graeffeCertificate`,
`KE02.coefficientCertificate`, `KE02.rootExtractionCertificate`,
`KE02.continuantCertificate`,
`KE02.localConstantsCertificate` and `KE02.wronskianCertificate`.

## Build and verify

The project pins Lean `v4.34.0-rc2` ([lean-toolchain](lean-toolchain)) and
Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`
([lake-manifest.json](lake-manifest.json)). Run from this directory, with the
toolchain's `bin` directory first on `PATH`:

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

The first Lake command downloads the official Mathlib cache: it places Mathlib
and the other dependencies, prebuilt at the pinned revisions, in
`.lake/packages`. A memory limit of 16 GB is sufficient.

`audit/verify.py` checks every Lean file and the configuration against
[audit/source-hashes.json](audit/source-hashes.json), and the definition and
statement files a second time against
[audit/statement-hashes.json](audit/statement-hashes.json); both manifests are
pinned by SHA256 inside the verifier, and the local import closure of
`KE02/Statement.lean` must consist of statement files. It rejects `sorry`,
`admit`, `axiom`, `native_decide`, `opaque`, compiler options,
metaprogramming, notation, instance and attribute declarations, `partial`, and
any `#` command outside the axiom probe. It requires the exact Lean version
output, the pinned and clean Mathlib checkout, deletes only this package's
build directory, rebuilds every module (all of which must be imported by
`KE02`), fails if any dependency is rebuilt, and requires the exact axiom
output. It then elaborates [audit/Probes.lean](audit/Probes.lean) and
requires each file in [audit/probes/](audit/probes/) to fail inside its final
example with its pinned kind of error.

The positive probes fix concrete values (for example `K = 7` for `n = 2`,
`K_b = 12` for `n = 2`, ties going left) and prove that weakened premises or
sharpened constants are false: the weight constant `4/3` cannot be lowered to
`5/4`, doubling the tolerance breaks the error bound `1/64`, (34) fails for
`θ = 1`, Bernoulli's `1/2` cannot be raised to `3/4`, and without the accuracy
premise Algorithm 2 can return a window with `S_h(t) = 3`. With exact replies
on that function the premises hold and the run refines at least once, so the
run theorem applies to a run that does not stop at the first test. Each
negative probe first elaborates a correct statement and then fails on a wrong
threshold, weight constant, tie rule, range of `θ`, radius constant or
stopping constant taken from the certificate, or on a use of the run theorem
without the accuracy premise.

`audit/test_verify.py` runs tamper controls on copies of the project: changed,
missing, extra and linked files, statement files commented out, unpinned or
malformed manifests, forged axiom output, forbidden tokens and commands,
misplaced or wrong-kind negative-probe failures, statement imports outside the
statement files, inexact toolchain output, a dirty Mathlib checkout, rebuilt
dependencies, failing commands, module reachability, and confinement of the
build-directory removal. Both scripts use
only the Python standard library and print the same output with and without
`-O`.
