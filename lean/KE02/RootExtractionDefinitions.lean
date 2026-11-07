import KE02.CoefficientDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Find

/-!
# Appendix A: root extraction from Graeffe coefficients

`graeffeCoeff r k j` is the coefficient `e_j` of `X^(n-j)` in the actual
`k`-th Graeffe iterate of `∏ (X + r_i)`. Indices are `0`-based: the root
`r i` corresponds to the paper's `r_(i+1)` and the ratio
`e_(i+1)/e_i` to the paper's `e_j/e_(j-1)` with `j = i+1`.
-/

noncomputable section

namespace KE02

/-- The coefficient `e_j` (descending degree order) of the actual `k`-th
Graeffe iterate of `∏ (X + r_i)`. -/
def graeffeCoeff {n : ℕ} (r : Fin n → ℝ) (k j : ℕ) : ℝ :=
  (graeffeIterate k (rootPolynomial r)).coeff (n - j)

/-- `r̂ = (e_(i+1)/e_i)^(1/R)` with `R = 2^k`. -/
def rootEstimate {n : ℕ} (r : Fin n → ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  (graeffeCoeff r k (i.val + 1) / graeffeCoeff r k i.val) ^ (1 / (2 ^ k : ℝ))

/-- `k` successive nonnegative square roots. -/
def iteratedSqrt (k : ℕ) (x : ℝ) : ℝ := Real.sqrt^[k] x

theorem exists_two_pow_ge (x : ℝ) : ∃ k : ℕ, x ≤ 2 ^ k :=
  (pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)).imp fun _ h => h.le

/-- The number of Graeffe steps: the least `k` with `8n/η ≤ 2^k`. For
`η > 0` this is the least `k` with `Rη ≥ 8n`, `R = 2^k`, as in Appendix A
(`RootExtractionCertificate.steps_least`). -/
def graeffeSteps (n : ℕ) (η : ℝ) : ℕ := Nat.find (exists_two_pow_ge (8 * n / η))

/-- Doubling `R`, starting from `R = 1`, and comparing `Rη` with `8n`, with at
most `fuel` doublings; returns the exponent `k` with `R = 2^k`. -/
def graeffeDoubling (n : ℕ) (η : ℝ) : ℕ → ℕ → ℝ → ℕ
  | 0, k, _ => k
  | fuel + 1, k, R => if 8 * (n : ℝ) ≤ R * η then k else graeffeDoubling n η fuel (k + 1) (2 * R)

end KE02
