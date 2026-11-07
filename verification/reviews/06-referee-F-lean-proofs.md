Reviewed: the Lean 4 project in lean/ (library KE02, aggregate `KE02.coreCertificate`): the proofs in lean/KE02/ and the audit tooling in lean/audit/.

# Referee report F: Lean 4 core of "A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices" (proofs and audit tooling)

**Verdict: ACCEPT WITH CHANGES.** All changes are minor hardening of the audit tooling. No soundness problem was found, and no change touches the mathematics.

The audit worked on a copy of the project; the project itself was not modified. File paths below are relative to lean/.

## Changes

1. `audit/probes/WrongStoppingConstant.lean:5` tests nothing in KE02: it only shows `norm_num` rejects a false arithmetic inequality (`1/4+1/128+1/64+1/4 < 1/2`). Tie it to `coreCertificate.algorithm2.stopping_constants` so it fails by type mismatch, or drop it and the matching claim at `README.md:92`.
2. `audit/verify.py:262` (`classify_negative`) only checks the line of the error. Pin the expected error per probe ("Type mismatch", "`assumption` failed", "`decide` proved", "unsolved goals"); otherwise a typo in a final example would also pass. All 7 probes currently fail for their stated reason (each message was read).
3. `audit/verify.py:74` (`FORBIDDEN`): add `notation|infix*|prefix|postfix|instance|attribute|export|partial`, at least for statement files. There are zero hits now.
4. `audit/verify.py:78` (`COMMAND`) only matches `#` commands at the start of a line. Lean also accepts `#eval` or `#exit` after other text on the same line, so match `#[A-Za-z_]` anywhere outside `audit/Axioms.lean`.
5. `audit/verify.py:200` (`check_statements`): also require that the import closure of `KE02/Statement.lean` stays inside `STATEMENT_FILES`. This holds today but is not enforced.
6. `KE02/Algorithm2Statement.lean:123` and `audit/Probes.lean`: the only satisfiability witness for the run premises (linear F, exact oracle) stops at the first test. Add a probe on a run that refines: the `corner` function from the probes with the exact oracle, n=2, δ=1/4 works ($`S_h(t)=3`$ at the start, so at least one refinement); proved in the auditor's own Lean file `NonVacuity.lean` (not part of the repository).
7. `audit/verify.py:312-318` (`check_toolchain`): require `git status --porcelain` on the Mathlib checkout to be empty (it is today), and compare the Lean version exactly rather than as a substring.

## Evidence by check

1. **Build:** `lake clean ke02` then `lake build` succeeded (3141 jobs). Only the 31 KE02 modules were built and there were no warnings.
2. **Axioms and grep:** the aggregate depends on exactly `[propext, Classical.choice, Quot.sound]`. The grep found only 3 `private` helper lemmas in `CoefficientBounds.lean`, the pinned `#print axioms`, harmless `decide`/`abbrev` uses, and no attributes, instances, notation, macros or options.
3. **Scripts and tampering:** `test_verify.py` gave 19/19 passing controls and `verify.py` passed all checks; under `-O` and hash seeds 0/1 the outputs were byte-identical with empty stderr. Three tamperings were each rejected with a clear message: changed statement constant ("Bound file changed"), added `sorry` (also "Bound file changed"), deleted proof module ("inventory differs ... missing"). With the manifests and pins also rewritten, the next layer still caught each one: "Statement file changed", "Disallowed token ... sorry", "Missing local import". With both manifests rewritten, Lean itself fails at `Algorithm2Proof.lean:681` (type mismatch).
4. **Probes:** all positive probes are correct by hand computation; `accuracy_premise_needed` is a real counterexample.
5. **Key proofs:** the Algorithm 2 run, Lemma 4.2 for general θ (it only needs $`0<\theta<1/2`$), the root-extraction bound and the 2⁻³⁴ chain are genuine and not circular. Satisfiable instances for each are proved in the auditor's own Lean file `NonVacuity.lean`, whose axioms are the standard three. An exact-fraction simulation (screening only) matched the run theorem on runs with 1–9 refinements.
6. **Hash inventory:** it covers all 40 .lean files, the 7 configuration files and the 19 statement files, and the verifier enforces it. The one file it cannot cover is `verify.py` itself, which holds the manifest pins; its sha256 at audit time was `29bcde6eca3fd437961701661631baa231e4413fcbed56b840ffba1ac9f5087e`.
