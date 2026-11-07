# Numerical experiments

This folder accompanies the paper

> **A Deterministic Algorithm for Eigenvalue Separation in Tridiagonal Matrices**

and contains the code, the raw data and the figure and table generators for the
numerical experiments. These experiments illustrate the behaviour of the
algorithm on test matrices. They are **not part of the proof**: the guarantees
of the paper (Proposition 3.1 and Theorem 4.2) are proved analytically and do
not depend on any computation in this folder.

## Setting and notation

Let $`T`$ be a real symmetric tridiagonal matrix of order $`n`$ with
$`\lVert T\rVert_2\le 1`$, let $`0<\delta<1/2`$ (all experiments use $`\delta=0.48`$), and let
$`X=\mathrm{diag}(1,\dots,n)`$. For $`t\in[0,\delta/n]`$ put $`H(t)=T+tX`$ and

```math
F(t)=\sum_{j=1}^{n} j\,\lambda_j(H(t)),\qquad
\mathcal S_h(t)=\frac{F(t+h)+F(t-h)-2F(t)}{h},
```

where $`\lambda_1\le\dots\le\lambda_n`$ are the eigenvalues. $`F`$ is convex, and
the endpoint slope variation of a window $`[t-h,t+h]`$ is

```math
\mathcal S_h^{(\theta)}(t)=\frac{F(t+h)-F(t+(1-2\theta)h)}{2\theta h}-\frac{F(t-(1-2\theta)h)-F(t-h)}{2\theta h}.
```

All code paths implement the selection loop of the improved selector of the paper
(Algorithm 2, Theorem 4.2): $`K=\lceil\log_2(16n^3)\rceil`$,
$`\theta=1/(4K)`$, start from $`t_0=h_0=\delta/(2n)`$; at refinement $`j`$ set
$`h_j=(1/2-\theta)h_{j-1}`$ and move to whichever of $`t_{j-1}\mp h_j`$ has the
smaller endpoint slope variation (ties go left). In the data files the endpoint
slope variation of the current window, $`d_j=\mathcal S_{h_j}^{(\theta)}(t_j)`$,
is stored as `d_hat` with error bound `d_err`.

The paper's local gap certificate (Proposition 3.1) and the selection
theorem, Theorem 4.2, read

```math
\mathcal S_h(t)<\tfrac12\ \Longrightarrow\ \mathrm{gap}(H(t))>\frac{h^2}{2^{20}n^4},
\qquad
\mathrm{gap}(T+D)>2^{-34}\,\frac{\delta^2}{n^{12}}\quad\text{for the returned } D=tX .
```

The universal bound $`2^{-34}\delta^2 n^{-12}`$ is stored in the data as
`cert_theory` and drawn as a dashed line in the gap figures.

## Two kinds of certificate

For a returned parameter and radius $`(t_*,h_*)`$ the experiments report

- the **slope certificate** $`g_{\mathrm S}=h_*^2/(2^{20}n^4)`$, which is valid as
  soon as $`\mathcal S_{h_*}(t_*)<1/2`$ is certified (Proposition 3.1; it applies
  to every input);
- the **direct certificate**
  $`g_{\mathrm{dir}}=\min_{1\le j<n}(\underline\lambda_{j+1}-\overline\lambda_j)`$,
  computed from rigorous eigenvalue enclosures
  $`\lambda_j(T+t_*X)\in[\underline\lambda_j,\overline\lambda_j]`$. It is a
  property of the instance and is not used by the selection theorem.

At the returned windows of the test matrices, $`g_{\mathrm{dir}}`$ is many orders of
magnitude larger than $`g_{\mathrm S}`$, and $`g_{\mathrm S}`$ is in turn far above the
universal bound.

### Stored slope certificates

When Algorithm 2 stops at refinement $`j`$ it returns $`(t_j,h_j)`$, and the
certificate of Proposition 3.1 is $`h_j^2/(2^{20}n^4)`$. Every stored slope
certificate has the form $`r^2/(2^{20}n^4)`$ with the following radius $`r`$:

| File | Field | Radius $`r`$ |
|---|---|---|
| `data/adaptive.jsonl` | `slope_cert` | $`h_{j_*}`$, at the first $`j`$ whose certified enclosure of $`\mathcal S_{h_j}(t_j)`$ is below $`1/2`$ |
| `data/adaptive.jsonl` | `full_K_cert` | $`h_K/2`$ |
| `data/directS_fp.jsonl`, `data/directS_hyb.jsonl` | `S_cert` | $`h_j`$, at `stop_j_S` |
| `data/directS_fp.jsonl`, `data/directS_hyb.jsonl` | `c8_cert` | $`h_j/2`$, at `stop_j_cert8` |
| `data/sweep.jsonl` | `heur_cert`, `cert8_cert`, `cert2_cert`, `practical_cert` | $`h_j/2`$, at `heur_j`, `cert8_j`, `cert2_j`, `practical_j` respectively |
| `data/sweep.jsonl` | `cert_final` | $`h_J/2`$, where $`J`$ is the last refinement performed (the first $`j`$ with $`\eta_j\ge1/8`$, or $`K`$) |
| `data/arb_<n>_<family>.json` | `cert_final` | $`h_K/2`$ |
| `run_fallback.py` (standard output) | `cert` | $`h_K/2`$ |

In the figures written by `make_figures.py`, the radius in the certificate labels
is $`h_j/2`$ for the double-precision sweep (`practical_cert`) and $`h_K/2`$ for
the dense rigorous runs (`cert_final`).

## Spectral-function oracles

| Backend | Where | What it computes |
|---|---|---|
| double precision (`fp`) | `ke02num/core.py`, `FPBackend` | $`F(t)`$ from LAPACK `dstemr` eigenvalues, with an a priori error model $`\eta`$ calibrated against ball arithmetic (`data/fp_calibration.json`). Decisions based on this model are called *fp-certified*; they are not rigorous. |
| dense ball arithmetic (`arb`) | `ke02num/core.py`, `ArbBackend` | rigorous enclosures of all eigenvalues of $`H(t)`$ with `python-flint` (`acb_mat.eig`), hence of $`F`$, $`\mathcal S_h`$, $`\mathcal S_h^{(\theta)}`$ and the gap. Cost is that of a dense high-precision eigensolver. |
| structured Sturm oracle (`hyb`) | `ke02num/hybrid.py`, `HybridBackend` | double-precision eigenpairs only seed the search; each eigenvalue bracket $`[\underline\lambda_j,\overline\lambda_j]`$ is certified by two Sturm counts evaluated in ball arithmetic on the exact matrix (exact $`d_i+t\,i`$ and $`\beta_i^2`$). Eigenvalues that cannot be separated share a cluster bracket that is counted collectively. Brackets can be narrowed rigorously by Sturm bisection (a Newton step only proposes split points). Quadratic cost in $`n`$ for a full set of brackets. |

The structured Sturm oracle is a practical certification tool. It is distinct
from the nearly linear exact-arithmetic oracle of Lemma 4.3, and its run times
say nothing about the arithmetic complexity of that lemma. All certificates
refer to the matrix whose entries are the double-precision numbers produced by
`make_matrix`.

## Matrix families

All matrices are generated by `ke02num.core.make_matrix(family, n, seed)` with
`numpy.random.default_rng(seed)`. Families marked "scaled" are divided by their
spectral radius (computed in double precision) so that $`\lVert T\rVert_2=1`$.

| `family` | Construction | Purpose |
|---|---|---|
| `random` | diagonal and off-diagonal entries i.i.d. uniform on $`[-1,1]`$; scaled | typical inputs |
| `nearly_reducible` | as `random`, then $`\max(2,\lfloor n/20\rfloor)`$ randomly chosen off-diagonal entries replaced by $`\pm10^{-9}`$; scaled | weakly coupled blocks |
| `two_blocks` | two identical random tridiagonal blocks joined by an off-diagonal entry $`10^{-7}`$; scaled | nearly repeated pairs |
| `wilkinson` | $`W_n^+`$: diagonal $`\lvert i-(n+1)/2\rvert`$, unit off-diagonal; scaled | extremely tight clusters |
| `toeplitz` | zero diagonal, off-diagonal $`1/2`$ (eigenvalues $`\cos(k\pi/(n+1))`$) | known structured spectrum |
| `diag_repeated` | off-diagonal $`0`$, diagonal drawn from $`\max(2,\lfloor n/2\rfloor)`$ equispaced values in $`[-1/2,1/2]`$ | exact multiplicities |

`toeplitz` and `wilkinson` are deterministic (seed 1 only); the other families
use seeds 1–30 in the sweeps and seed 1 for single representative runs.

## Layout

| Path | Contents |
|---|---|
| `ke02num/core.py` | matrix families, $`F`$, $`\mathcal S_h`$, $`\mathcal S_h^{(\theta)}`$, the selector `run_algorithm`, the `fp` and `arb` backends, baseline perturbations |
| `ke02num/hybrid.py` | structured Sturm oracle `HybridBackend` |
| `run_sweep.py` | double-precision sweep (selection path, early stopping, baselines) and error-model calibration |
| `run_arb.py` | dense ball-arithmetic runs of all $`K`$ refinements, with validation of the double-precision path |
| `run_direct_s.py` | centered test $`\mathcal S_{h_j}(t_j)<1/2`$ versus endpoint test $`d_j<1/8`$ (double precision), and runs with the structured oracle |
| `run_adaptive.py` | adaptive-precision certified pipeline used in Section 5 of the paper |
| `run_fallback.py` | rigorous run of all $`K`$ refinements with rigorously decided endpoint comparisons (prints a summary, writes no file) |
| `make_figures.py` | figures in `figures/` and tables in `tables/` from the sweep and dense runs |
| `data/` | raw results (see below) |
| `figures/`, `tables/` | generated figures (PDF and PNG) and LaTeX table bodies |
| `requirements.txt`, `LICENSE` | Python requirements; MIT licence |

## Data files

| File | Produced by | Contents |
|---|---|---|
| `data/sweep.jsonl` | `run_sweep.py` | one record per (family, $`n`$, seed), $`n\in\{10,20,50,100,200\}`$: full selection path with $`d_j`$, $`\eta_j`$ and $`\mathcal S_{h_j/2}(t_j)`$; first $`j`$ with $`d_j+\eta_j<1/8`$ (`cert8_j`) and with $`d_j+\eta_j<1/2`$ (`cert2_j`); the gap and the certificate $`(h_j/2)^2/(2^{20}n^4)`$ at the first $`j`$ with $`d_j+\eta_j<1/8`$, or at the last iterate with $`\eta_j<1/8`$ if there is none (`practical_*`); baseline perturbations (`baselines`) |
| `data/fp_calibration.json` | `run_sweep.py` | maximum ratio of the observed double-precision error of $`F`$ to its a priori error model |
| `data/arb_<n>_<family>.json` | `run_arb.py` | dense ball-arithmetic run of all $`K`$ refinements, seed 1, $`n\in\{10,20,50,100\}`$, with the double-precision run on the same matrix (`fp_*`) |
| `data/directS_fp.jsonl` | `run_direct_s.py A` | double precision, $`n\le1000`$: first $`j`$ with $`\mathcal S_{h_j}(t_j)+\eta<1/2`$ (`stop_j_S`) and with $`d_j+\eta_j<1/8`$ (`stop_j_cert8`), with gaps and certificates at both |
| `data/directS_hyb.jsonl` | `run_direct_s.py B 100 200 500 1000` | the same test with the structured oracle, without bracket refinement, seed 1 |
| `data/adaptive.jsonl` | `run_adaptive.py` | certified pipeline, seed 1, all families for $`n=50,100,200`$ and `diag_repeated`, `toeplitz` for $`n=500`$: $`j_*`$ (`j_star`), $`h_*`$, $`t_*`$, $`g_{\mathrm S}`$ (`slope_cert`), $`g_{\mathrm{dir}}`$ (`gap_direct_refined`), wall times of the double-precision path (`wall_stage1`) and of the certification (`wall_stage23`), and, per window $`j`$, the midpoint `S2` and radius `e2` of the enclosure of $`\mathcal S_{h_j}(t_j)`$, with `S3`, `e3` after refinement (`log`) |

`run_adaptive.py` works as follows. The double-precision selection path is
computed first. Each window is then tested with the structured oracle, and if
the enclosure cannot decide $`\mathcal S_{h_j}(t_j)<1/2`$, the three values of
$`F`$ are refined. The first window whose certified upper bound is below $`1/2`$
gives $`j_*`$.

## Requirements

From `requirements.txt`:

```
numpy>=2.0
scipy>=1.14
matplotlib>=3.10
pandas>=2.0
python-flint>=0.7
```

`python-flint` provides the ball arithmetic and is needed by `run_sweep.py`
(calibration), `run_arb.py`, `run_adaptive.py`, `run_fallback.py` and part B of
`run_direct_s.py`. `make_figures.py` needs only numpy, scipy, pandas and
matplotlib. The requirement matplotlib 3.10 or later is needed because
`make_figures.py` uses the `orientation` argument of `Axes.boxplot`.

## Reproduction

Run all commands from this folder.

```bash
pip install -r requirements.txt

python3 run_sweep.py                       # data/fp_calibration.json, data/sweep.jsonl (overwritten)
python3 run_arb.py 10 20 50 100            # data/arb_<n>_<family>.json (existing files are skipped)
python3 run_direct_s.py A                  # data/directS_fp.jsonl (overwritten)
python3 run_direct_s.py B 100 200 500 1000 # appends to data/directS_hyb.jsonl
python3 run_adaptive.py 50 100 200         # appends to data/adaptive.jsonl
python3 run_adaptive.py 500 --families diag_repeated toeplitz
python3 run_fallback.py                    # summary on standard output
python3 make_figures.py                    # figures/ and tables/ from data/
```

`run_direct_s.py B` and `run_adaptive.py` append to their output files, so
delete those files first to regenerate them from scratch. Wall times depend on
the machine. Double-precision quantities can differ in the last digits between
LAPACK builds.

`make_figures.py` reads `data/sweep.jsonl`, `data/arb_*.json` and
`data/fp_calibration.json`, and writes:

| Output | Content |
|---|---|
| `figures/ke02_gap_vs_certificate.{pdf,png}` | $`\mathrm{gap}(T+t_*X)`$ and the certificate at the fp-certified stopping point (median and range over seeds), the dense rigorous runs of all $`K`$ refinements, $`\mathrm{gap}(T)`$, and the bound $`2^{-34}\delta^2n^{-12}`$, against $`n`$ |
| `figures/ke02_early_stopping.{pdf,png}` | (a) $`d_j`$ along the path for `random`, $`n=50`$, seed 1 (double precision and ball arithmetic); (b) first $`j`$ with $`d_j+\eta_j<1/8`$ against $`n`$, compared with $`K`$ |
| `figures/ke02_baselines.{pdf,png}` | $`\mathrm{gap}(T+D)`$ at $`n=100`$ for $`D=0`$, the ramp $`(\delta/n)X`$, a random $`t`$, a random diagonal with $`\lvert D_{ii}\rvert\le\delta`$, the selector, and the best $`t`$ on a grid |
| `figures/ke02_gap_profile.{pdf,png}` | $`t\mapsto\mathrm{gap}(T+tX)`$ on $`[0,\delta/n]`$ with the selected windows, `two_blocks`, $`n=50`$, seed 1 (recomputed in double precision; no data file) |
| `tables/table_sweep.tex` | per family and $`n`$: $`K`$, $`d_0`$, stopping indices, certified fraction, evaluations, gaps, certificate, $`\log_{10}`$ of gap/certificate |
| `tables/table_arb.tex` | dense rigorous runs: final $`d_K`$ with radius, rigorous gap with radius, certificate, agreement of the double-precision path |
| `tables/table_baselines.tex` | median gaps of the perturbations at $`n=100`$, ratio of the selector to the grid optimum, and how often the selector is at least as good as the random perturbations |
| `tables/summary.json` | summary statistics of the sweep and the dense runs |

## Correspondence with Section 5 of the paper

All records below are for seed 1 except where seeds are stated; $`\delta=0.48`$.

| Paper | File and records | Fields |
|---|---|---|
| Table 1 (test families) | `ke02num/core.py` | `make_matrix` |
| Table 2 (representative certified runs) | `data/adaptive.jsonl`: (`random`, 100), (`toeplitz`, 100), (`random`, 200), (`wilkinson`, 200), (`toeplitz`, 200), (`diag_repeated`, 500), (`toeplitz`, 500) | $`K`$ = `K`; $`j_*`$ = `j_star`; $`g_{\mathrm S}`$ = `slope_cert`; $`g_{\mathrm{dir}}`$ = `gap_direct_refined`; time = `wall_stage1` + `wall_stage23` |
| Figure 4(a) | `data/adaptive.jsonl`: (`random`, 100) and (`toeplitz`, 100) | for each entry of `log`: `j` against `S2` + `e2` (upper end of the certified enclosure of $`\mathcal S_{h_j}(t_j)`$) |
| Figure 4(b) | `data/adaptive.jsonl`: all 20 records | `j_star` against `n`; the staircase is $`K=\lceil\log_2(16n^3)\rceil`$ |
| Figure 5 | `data/adaptive.jsonl`: all 20 records | `gap_direct_refined` (circles) and `slope_cert` (squares) against `n`; the dashed line is $`2^{-34}\delta^2n^{-12}`$ |
| Figure 6(a) | `data/adaptive.jsonl`: all 20 records | `wall_stage1` + `wall_stage23` against `n` |
| Figure 6(b) | `data/adaptive.jsonl`: the six records with $`n=200`$ | `wall_stage23` (Sturm certification and refinement) with `wall_stage1` (double-precision path selection) stacked on top |
| Figure 7, distributions | `data/sweep.jsonl` and `data/directS_fp.jsonl`: $`n=100`$, seeds 1–30 (seed 1 for `wilkinson`, `toeplitz`) | `baselines.none`, `baselines.ramp_max`, `baselines.random_t`, `baselines.random_diag`, `baselines.oracle_grid` from `sweep.jsonl`; `S_gap` from `directS_fp.jsonl` |
| Figure 7, stars | `data/adaptive.jsonl`: the six records with $`n=100`$ | `gap_direct_refined` |

Figures 4–7 of the paper are plotted from exactly these files and fields. The
plotting code for these four figures is not included in this folder.

## Licence

MIT; see `LICENSE`.
