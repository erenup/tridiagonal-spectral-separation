import KE02.RootExtractionDefinitions
import KE02.CoefficientStatement

/-!
# Statement: Appendix A, from coefficients to the weighted eigenvalue sum

The roots are positive reals in nonincreasing order; in the paper they are
`r_j = 2 + λ_j(A)`, which lie in `(0, 4)` because `‖A‖₂ < 2` (that spectral
fact is a premise here). `λ_j = r_(n+1-j) - 2` is written `r j.rev - 2`.
-/

namespace KE02

structure RootExtractionCertificate : Prop where
  /-- The coefficients of the actual Graeffe iterate are the elementary
  symmetric functions of the powered roots. -/
  graeffe_coeff : ∀ (n : ℕ) (r : Fin n → ℝ) (k j : ℕ), graeffeCoeff r k j = elementaryCoeff r k j
  /-- `p_j ≤ e_j ≤ 2^n p_j`. -/
  coeff_bounds : ∀ (n : ℕ) (r : Fin n → ℝ) (k j : ℕ), (∀ i, 0 < r i) → Antitone r → j ≤ n →
    leadingRootProduct r k j ≤ graeffeCoeff r k j ∧
      graeffeCoeff r k j ≤ (2 : ℝ) ^ n * leadingRootProduct r k j
  /-- (43): `r_j 2^(-n/R) ≤ (e_j/e_(j-1))^(1/R) ≤ r_j 2^(n/R)`, `R = 2^k`. -/
  ratio_root : ∀ (n : ℕ) (r : Fin n → ℝ) (k : ℕ) (i : Fin n), (∀ a, 0 < r a) → Antitone r →
    r i * (2 : ℝ) ^ (-(n : ℝ) / 2 ^ k) ≤ rootEstimate r k i ∧
      rootEstimate r k i ≤ r i * (2 : ℝ) ^ ((n : ℝ) / 2 ^ k)
  /-- The `R`-th root is `k` successive nonnegative square roots. -/
  iterated_sqrt : ∀ (k : ℕ) (x : ℝ), 0 ≤ x → iteratedSqrt k x = x ^ (1 / (2 ^ k : ℝ))
  /-- `2^x - 1 ≤ x` for `0 ≤ x ≤ 1`. -/
  two_rpow_sub_one_le : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 : ℝ) ^ x - 1 ≤ x
  /-- `|r̂_j - r_j| ≤ 4n/R` when `0 < r_j < 4` and `n ≤ R`. -/
  root_error : ∀ (n : ℕ) (r : Fin n → ℝ) (k : ℕ) (i : Fin n), (∀ a, 0 < r a) → Antitone r →
    r i < 4 → (n : ℝ) ≤ 2 ^ k → |rootEstimate r k i - r i| ≤ 4 * n / 2 ^ k
  /-- Appendix A: `k` is the least integer with `Rη ≥ 8n`, `R = 2^k`. -/
  steps_least : ∀ (n : ℕ) (η : ℝ), 0 < η →
    8 * (n : ℝ) ≤ 2 ^ graeffeSteps n η * η ∧ ∀ k < graeffeSteps n η, (2 : ℝ) ^ k * η < 8 * n
  /-- It is found by doubling `R` from `R = 1` and comparing `Rη` with `8n`:
  with any budget of at least `k` doublings, the search returns `k`. -/
  steps_doubling : ∀ (n : ℕ) (η : ℝ) (fuel : ℕ), 0 < η → graeffeSteps n η ≤ fuel →
    graeffeDoubling n η fuel 0 1 = graeffeSteps n η
  /-- The doubling choice of `k`: `8n/η ≤ R < 16n/η`, hence `n ≤ R` and
  `4n/R ≤ η/2`. -/
  steps_choice : ∀ (n : ℕ) (η : ℝ), 1 ≤ n → 0 < η → η < 1 →
    8 * (n : ℝ) / η ≤ 2 ^ graeffeSteps n η ∧ (2 : ℝ) ^ graeffeSteps n η < 16 * n / η ∧
      (n : ℝ) ≤ 2 ^ graeffeSteps n η ∧ 4 * (n : ℝ) / 2 ^ graeffeSteps n η ≤ η / 2
  /-- With `η = ε/Σ_j j`, errors `η/2` in every `λ_j` give error `≤ ε` in `Σ_j j λ_j`. -/
  weighted_error : ∀ (n : ℕ) (lam lamHat : Fin n → ℝ) (ε : ℝ), 0 ≤ ε →
    (∀ j, |lamHat j - lam j| ≤ ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) →
    |∑ j : Fin n, ((j : ℝ) + 1) * lamHat j - ∑ j : Fin n, ((j : ℝ) + 1) * lam j| ≤ ε
  /-- Section 4.3: errors `η` give error `≤ n(n+1)η/2`. -/
  sum_error : ∀ (n : ℕ) (lam lamHat : Fin n → ℝ) (η : ℝ),
    (∀ j, |lamHat j - lam j| ≤ η) →
    |∑ j : Fin n, ((j : ℝ) + 1) * lamHat j - ∑ j : Fin n, ((j : ℝ) + 1) * lam j| ≤
      (n : ℝ) * (n + 1) / 2 * η
  /-- The scalar pipeline of Appendix A: `η = ε/Σ_j j`, `k` by doubling,
  `λ̂_j = r̂_(n+1-j) - 2` with `r̂` from `k` square roots of the coefficient
  ratios, matched index by index: `|λ̂_j - λ_j| ≤ η/2` and
  `|Σ_j j λ̂_j - Σ_j j λ_j| ≤ (n(n+1)/2)(η/2) ≤ ε`. -/
  pipeline : ∀ (n : ℕ) (r : Fin n → ℝ) (ε : ℝ), 1 ≤ n → (∀ a, 0 < r a ∧ r a < 4) →
    Antitone r → 0 < ε → ε < 1 →
    Monotone (fun j : Fin n => r j.rev - 2) ∧
    (∀ j : Fin n,
      |(iteratedSqrt (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1)))
          (graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) (j.rev.val + 1) /
            graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) j.rev.val) - 2) -
        (r j.rev - 2)| ≤ ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) ∧
    |∑ j : Fin n, ((j : ℝ) + 1) *
        (iteratedSqrt (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1)))
          (graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) (j.rev.val + 1) /
            graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) j.rev.val) - 2) -
      ∑ j : Fin n, ((j : ℝ) + 1) * (r j.rev - 2)| ≤
        (n : ℝ) * (n + 1) / 2 * (ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) ∧
    (n : ℝ) * (n + 1) / 2 * (ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) ≤ ε

end KE02
