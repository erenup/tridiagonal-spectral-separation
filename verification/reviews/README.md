# Review record

These reports record the independent informal AI-agent audits of the paper
and of its Lean formalization. Each auditor worked separately from the other
auditors, was not an author of the material it reviewed, derived and checked
every step itself, and ran its own exact tests or builds. Each report states
what was read before its auditor's own derivation was written and what was
consulted only afterwards. No report claims formal certification or external
peer review.

| Report | Scope | Verdict |
|---|---|---|
| [01](01-referee-A-earlier-draft.md) | An earlier 27-page draft of the paper against the catalogue statement of KE-02: the gap theorem, the complete target including the operation count and the model of computation, every lemma, both algorithms and the oracle of Appendix A, with independent exact and high-precision tests | Gap theorem and full target: accept with corrections (C1 to C12, of which C1 to C4 mandatory); no mathematical error |
| [02](02-referee-B-earlier-draft.md) | Same scope, independent adversarial referee | Gap theorem and full target: accept with corrections (editorial items 1 to 9); no mathematical error |
| [03](03-referee-C-final-text.md) | The 28-page text against the catalogue statement, including a check of the corrections made since the earlier draft, with the referee's own exact checker and negative controls | Gap theorem: accept; full target: accept with corrections (wording only, items 1 to 14); no mathematical gap or error |
| [04](04-referee-D-final-text.md) | Same scope, independent referee | Gap theorem and full target: accept; text: accept with corrections (C1 to C10); no mathematical gap or error |
| [05](05-referee-E-lean-statements.md) | Fidelity of the Lean proposition `KE02.CoreCertificate` and the definitions it uses to the paper, and the scope claims of the Lean guide and scope file (statements only) | Accept with changes: wording in the guide, the scope file and two docstrings; no Lean statement to change |
| [06](06-referee-F-lean-proofs.md) | The Lean proofs of `KE02.coreCertificate` and the audit tooling: clean build, axioms, source audit, tampering, negative probes | Accept with changes: hardening of the audit tooling; no soundness problem |

Report 01 is by referee A, 02 by B, 03 by C, 04 by D, 05 by E and 06 by F:
six different auditors. The two reports on each version of the paper are by
different referees, and the Lean statements and the Lean proofs were
reviewed by different referees. Scripts and Lean files that the reports
describe as the referee's own are not part of the repository.

## Corrections

No report found a mathematical error or gap, and none requested a
mathematical correction to the text. The corrections requested in
reports 01 to 04 concern statements, exposition, wording and references, and
all are incorporated in the [paper source](../../paper/main.tex). In the
table, line numbers refer to `paper/main.tex` unless another file is named.

| Requested in | Correction | Location in the source |
|---|---|---|
| 01 C1, C3; 02 item 1 | The explicit constant $`2^{-34}`$ in the abstract and in (6), and both forms of the bound | lines 57, 288; (5) at lines 192–198 |
| 01 C1, C2; 02 item 2 | Unconditional cost statements in the abstract and in Section 6; the eigenvalue-solver route only as an alternative | lines 64–67, 2533–2537; 2029–2051 |
| 01 C3, C6; 02 item 3 | A main theorem with the gap, the budget, the operation count and the model; the exponent named $a$ in (3); $q=3$; the per-call cost of Lemma 4.3 with its accounting | Theorem 1.1, lines 185–209; lines 133–135, 2075–2079, 1999, 2004–2027; proof of Theorem 1.1, lines 2081–2109 |
| 01 C4; 02 item 4; 03 item 1; 04 C10 | $K$, $k$ and $`K_{\mathrm b}`$ found by doubling or repeated multiplication and comparisons; no logarithm, floor or bit extraction as a primitive operation | lines 1759–1761, 1434–1436, 2683–2687; 205–207, 2107–2108 |
| 02 item 4 | Complex numbers as pairs of reals; off-diagonal entries only through $`c_i=\lvert A_{i,i+1}\rvert^2`$, with no phase gauge computed; the labelling $`r_j=2+\lambda_{n+1-j}(A)`$ | lines 203–205, 2643–2650, 2666–2667 |
| 01 C5; 02 item 4 | $`\widehat\lambda_j=\widehat r_{n+1-j}-2`$ and the index-wise matching | lines 2697–2707 |
| 01 C7 | The secant chain in the proof of Lemma 4.2 | lines 1826–1857 |
| 01 C8; 02 item 5 | Lemma 3.1: the weighted-average choice of $q$, the case (c) bound, the number of path steps and the triangle inequality | lines 942–957, 1083–1090, 1092–1107 |
| 02 item 6 | The three nuclear-norm bounds in the proof of Lemma 3.2 | lines 1295–1309 |
| 02 item 7 | The window $`[t-h,t+h]\subseteq[0,\delta/n]`$ in Theorem 4.2 | lines 1880, 1920–1925 |
| 01 C9 | One title in the text and the PDF metadata | lines 16, 35 |
| 01 C11; 02 item 8 | Section 5 as an illustration: $`j_*`$ is the first certified stop along an uncertified double-precision path, in the text, the outline and the captions | lines 304, 436–439, 2172, 2180–2189, 2252–2257, 2416–2421 |
| 03 item 2; 04 C10 | The growth of the Graeffe coefficients and the absence of a bit-complexity bound | lines 2712–2716 |
| 03 items 3, 4; 04 C2, C3, C4 | Notation and entries in Examples 3.1 and 3.2 | lines 857, 859, 896, 899, 1168–1171, 1177, 1192, 1206–1207, 1211; `matrix_with_cut.tex`, line 3 |
| 03 item 5 | The closing lines of both algorithms | lines 1460, 1789 |
| 03 item 6 | The output $D=tX$ and its $n$ multiplications | lines 189–191, 2097–2098 |
| 03 items 7, 8; 04 C5 | Unsupported numerical claims removed from Section 1 | lines 312–314 |
| 03 item 9; 04 C6 | The rigorous fallback run described and located | lines 2258–2262 |
| 03 items 10, 11; 04 C7 | Process wording and figure texts | lines 2301, 2366, 2377–2378, 2394, 2406, 2440–2442, 2458–2459, 2481, 2513; the figure files `ke02_iterations_certified.png` and `ke02_strict_runtime.png`, included at lines 2296 and 2404 |
| 03 item 13; 04 C9 | Bibliography: arXiv identifiers, protected capitals, volume and pages | `refs.bib`, lines 49, 164, 180, 185, 221, 240 |
| 03 item 14 | The specific result of Sobczyk cited | lines 2032–2037 |
| 04 C8 | Lemma 4.1 stated for every refinement that is performed | lines 1515–1517 |

Report 03 also noted that the lower side of the root-extraction error bound
was not stated; it now is, at lines 2689–2691. Report 01 C12 left the form of
the declaration on the use of AI tools to the authors; it is at lines
2629–2636. Item 9 of report 02 is an observation that the certificate is
conservative rather than a requested change; the paper states this
conservatism at lines 2343–2355, 2515–2520 and 2543–2548.

Four requests are release preconditions about the contents of this
repository rather than corrections of the paper: report 01 C10 and the
second half of report 02 item 1 (the repository guide must state the
constant $`2^{-34}`$), report 03 item 12 and report 04 C1 (the folder
`verification/numerics/` linked at lines 2186–2189 and 2623–2627 must
contain the code and data of Section 5, and the repository guide must give
this paper's title and constants). They are satisfied: the
[repository guide](../../README.md) gives the title, Theorem 1.1 and the
constants $a=12$, $`c_0=2^{-34}`$ and $q=3$, and no other gap constant, and
[verification/numerics/](../numerics/README.md) contains the code, data,
figures and tables of Section 5, including `run_fallback.py`.

The Lean reports requested only wording and hardening changes, listed
below. All are made.

## Relation of the reviewed files to the repository

- **Reports 01 and 02** reviewed an earlier 27-page draft of the paper
  (single source file with SHA256 `02520239…8a4c`). No source file of the
  current [paper/](../../paper/) is byte-identical to its counterpart in
  that draft; five of the seven figure files are. The current paper adds
  Theorem 1.1 and its proof, which shifts equation numbers by one from (5)
  on, and contains the corrections listed above; the other numbered results
  keep their numbers.
- **Reports 03 and 04** reviewed the 28-page text in the state before the
  corrections listed below: `paper/main.tex` with SHA256
  `6428c025…40ec` (2719 lines), `paper/main.pdf` with SHA256
  `a8b92e60…5001`, and `refs.bib`, `matrix_with_cut.tex`,
  `vectors_with_cut.tex` and the figures of that state. The line numbers they
  cite refer to that source. Since then, only changes that they requested or
  noted were made; no mathematical claim changed. By type, with lines of
  the current `paper/main.tex`:
  - Wording of the model of computation and of the output: lines 189–191
    and 205–207 in Theorem 1.1, 2097–2098 and 2107–2108 in its proof, and
    2686–2687 in Appendix A.
  - Appendix A: the two-sided form of the root-extraction bound, lines
    2690–2691, and the coefficient growth with the absence of a
    bit-complexity bound, lines 2712–2716.
  - Algorithms: the search for $`K_{\mathrm b}`$, lines 1434–1436, and the
    closing lines 1460 and 1789; the wording of Lemma 4.1, lines 1515–1517.
  - Examples 3.1 and 3.2: notation and entries, lines 857, 859, 896, 899,
    1168–1171, 1177, 1192, 1206–1207 and 1211, and `matrix_with_cut.tex`,
    line 3.
  - Numerical claims and process wording: lines 312–314 in Section 1, the
    fallback run at lines 2258–2262, and lines 2301, 2366, 2377–2378, 2394,
    2406, 2440–2442, 2458–2459, 2481 and 2513 in Section 5.
  - Figures: `ke02_iterations_certified.png` and `ke02_strict_runtime.png`
    replace the PDF versions of Figures 4 and 6 (lines 2296 and 2404), with
    the footer lines removed and the first panel of Figure 6 titled "Total
    runtime"; the plotted data are unchanged. The other five figure files
    and `vectors_with_cut.tex` are byte-identical to the reviewed ones.
  - References: the citation and description of Sobczyk's result, lines
    2032–2037 and 2146, and six entries of `refs.bib` (lines 49, 164, 180,
    185, 221 and 240).

  The numbered results, their titles and the equation numbers are unchanged;
  the PDF still has 28 pages, and some results moved by one page.

  Reports 02 and 03 number some equations by section and report 03 numbers
  two figures differently; in the numbering of `paper/main.pdf`, report 02's
  (1.5) and (A.1) are (6) and (43), and report 03's (2.2), (2.6), (2.8),
  (3.3), (4.4), (4.5) and (A.1) are (8), (12), (14), (22), (34), (36) and
  (43), its Fig. 3 is Figure 4 and its Fig. 5(a) is Figure 6(a).
- **Reports 05 and 06** reviewed the same state of the Lean project, the one
  pinned by `audit/verify.py` with SHA256
  `29bcde6eca3fd437961701661631baa231e4413fcbed56b840ffba1ac9f5087e`, and
  report 05 compared it with the paper text reviewed in reports 03 and 04.
  Since then, the following changes were made.
  - Requested in report 05: the wording of [lean/README.md](../../lean/README.md)
    (its changes 1, 2, 3, 6 and 7, in the result table and the paragraph
    after it) and of [lean/SCOPE.md](../../lean/SCOPE.md) (changes 4 and 6,
    lines 84–85, 88–90 and 190–192); the docstrings of
    `KE02/Algorithm2Statement.lean`, lines 81–82 and 105 (change 5), and of
    `KE02/ContinuantStatement.lean`, line 13 (change 7).
  - Requested in report 06: `audit/probes/WrongStoppingConstant.lean` now
    takes its constant from `coreCertificate.algorithm2.stopping_constants`
    and fails by a type mismatch (change 1); `audit/verify.py` pins the kind
    of error of every negative probe (change 2), forbids `notation`,
    `infix`, `infixl`, `infixr`, `prefix`, `postfix`, `instance`,
    `attribute`, `export` and `partial` (change 3), rejects a `#` command
    anywhere outside the axiom probe (change 4), requires the local import
    closure of `KE02/Statement.lean` to consist of statement files
    (change 5), compares the Lean version output exactly and requires a clean
    Mathlib checkout (change 7); and `audit/Probes.lean` adds the theorem
    `refining_run`, a run with $n=2$ and $`\delta=1/4`$ that refines at least
    once and satisfies the premises of the run theorem (change 6).
    `audit/test_verify.py` gained controls for these checks (21 in all), and
    the guide describes them.
  - Not requested: a comment in `KE02/CoefficientBounds.lean`, line 52,
    now reads "leading product" instead of "prefix product"; the build
    instructions of the guide now start with `lake exe cache get`; and four
    page references in the guide's result table and two in the scope file
    were corrected against `paper/main.pdf`.
  - The manifests `audit/statement-hashes.json` and `audit/source-hashes.json`
    and the two digests inside `audit/verify.py` were pinned again.

  Of the 19 entries of `audit/statement-hashes.json`, 17 are identical to the
  entries pinned at review time, including `KE02/Statement.lean`
  (`3c047d4d…fcc1`) and `KE02/Algorithm2Definitions.lean` (`5917772c…f60a`),
  whose hashes report 05 quotes. The other two differ only in the docstrings
  above: `KE02/Algorithm2Statement.lean`, quoted in report 05 as
  `4ed93597…fced`, now `edb23795…9cdc`, and `KE02/ContinuantStatement.lean`.
  Apart from these two docstrings, the comment in
  `KE02/CoefficientBounds.lean` and the two probe files, every Lean source
  file, the Lake configuration, the lockfile and the toolchain file are
  byte-identical to the reviewed ones.
