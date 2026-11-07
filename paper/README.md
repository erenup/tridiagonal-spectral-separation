# A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices

Authors: Wenqi Zhu; Ping Nie.

Wenqi Zhu — Mathematical Institute, Woodstock Road, University of Oxford, Oxford, UK, OX2 6GG — wenqi.zhu@maths.ox.ac.uk

Ping Nie — David R. Cheriton School of Computer Science, University of Waterloo — ping.nie@uwaterloo.ca

The [paper](main.pdf) proves, in Theorem 1.1, that for every $n\geq2$,
every $`0<\delta<1/2`$ and every Hermitian tridiagonal
$`T\in\mathbb C^{n\times n}`$ with $`\lVert T\rVert_2\leq1`$, a deterministic
algorithm computes $`t\in[0,\delta/n]`$ such that $D=tX$, with
$`X=\mathrm{diag}(1,\ldots,n)`$, satisfies $`\lVert D\rVert_2\leq\delta`$ and
$`\mathrm{gap}(T+D)>2^{-34}\delta^2n^{-12}\geq2^{-34}(\delta/n)^{12}`$, using
$`O(n[1+\log(n/\delta)]^3)`$ exact arithmetic operations, comparisons and
square roots. The proof combines a convex weighted eigenvalue sum and its
finite-scale slope variation with a tridiagonal localization argument
(Sections 2 and 3), an adaptive interval selector that stops after at most
$`\lceil\log_2(16n^3)\rceil`$ refinements (Section 4), and an exact-arithmetic
spectral-function oracle built from the determinant recurrence and Graeffe
root-squaring (Lemma 4.3 and Appendix A); Section 5 gives numerical
illustrations.

The source is [main.tex](main.tex), with two included TikZ fragments,
[matrix_with_cut.tex](matrix_with_cut.tex) and
[vectors_with_cut.tex](vectors_with_cut.tex), the seven figure files it
includes, and the bibliography [refs.bib](refs.bib). Build from this
directory with LaTeX, BibTeX and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape -outdir=build/ci main.tex
```

The rebuilt PDF is `build/ci/main.pdf`. The included `main.pdf` has the
same content, 28 pages. Standard TeX Live packages, including `amsthm`,
`natbib`, `algorithm2e`, `tikz`, `xurl`, `hyperref` and `cleveref`, suffice.
The source and PDF list the authors above. [SHA256SUMS](SHA256SUMS) lists the
SHA-256 of every other file in this directory.

The finite and scalar core of the argument is formalized in Lean and the
constants and the algebra of Appendix A are checked exactly; see the
[section-by-section map](../paper-lean-mapping/by-section.md) for the evidence
attached to each numbered result. The spectral theory, the localization
argument as matrix statements, the oracle as an algorithm, the operation
counts and Theorem 1.1 as a whole follow from the written proofs.

All files in this directory, including the manuscript source and PDF, are
licensed under [CC BY-SA 4.0](LICENSE).
