import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Statement: the discrete Wronskian identity (22)

Coordinates are `1, …, n`. The eigenvector equations at coordinate `i` are
written exactly as in Step 2 of the proof of Lemma 3.1,
`β_(i-1) u_(i-1) + d_i u_i + β_i u_(i+1) = λ u_i`, with the boundary
convention `β_0 = 0`. The determinant of the rows `r_i, r_(i+1)` is
`(u₁)_i (u₂)_(i+1) - (u₁)_(i+1) (u₂)_i`.
-/

namespace KE02

structure WronskianCertificate : Prop where
  /-- (22). -/
  identity : ∀ (n : ℕ) (d β a b : ℕ → ℝ) (lam mu : ℝ), β 0 = 0 →
    (∀ i, 1 ≤ i → i ≤ n → β (i - 1) * a (i - 1) + d i * a i + β i * a (i + 1) = lam * a i) →
    (∀ i, 1 ≤ i → i ≤ n → β (i - 1) * b (i - 1) + d i * b i + β i * b (i + 1) = mu * b i) →
    ∀ i ≤ n, β i * (a i * b (i + 1) - a (i + 1) * b i) =
      (mu - lam) * ∑ j ∈ Finset.Icc 1 i, a j * b j
  /-- Step 2: for orthonormal `u₁, u₂`, `|Σ_(j ≤ i) (u₁)_j (u₂)_j| ≤ 1/2`. -/
  partial_inner : ∀ (n : ℕ) (a b : ℕ → ℝ),
    ∑ j ∈ Finset.Icc 1 n, a j ^ 2 = 1 → ∑ j ∈ Finset.Icc 1 n, b j ^ 2 = 1 →
    ∑ j ∈ Finset.Icc 1 n, a j * b j = 0 →
    ∀ i ≤ n, |∑ j ∈ Finset.Icc 1 i, a j * b j| ≤ 1 / 2
  /-- Step 2: `|β_i| |det(r_i, r_(i+1))| ≤ γ/2` when `|λ - μ| ≤ γ`. -/
  bound : ∀ (n : ℕ) (d β a b : ℕ → ℝ) (lam mu γ : ℝ), β 0 = 0 →
    (∀ i, 1 ≤ i → i ≤ n → β (i - 1) * a (i - 1) + d i * a i + β i * a (i + 1) = lam * a i) →
    (∀ i, 1 ≤ i → i ≤ n → β (i - 1) * b (i - 1) + d i * b i + β i * b (i + 1) = mu * b i) →
    ∑ j ∈ Finset.Icc 1 n, a j ^ 2 = 1 → ∑ j ∈ Finset.Icc 1 n, b j ^ 2 = 1 →
    ∑ j ∈ Finset.Icc 1 n, a j * b j = 0 → |lam - mu| ≤ γ →
    ∀ i ≤ n, |β i| * |a i * b (i + 1) - a (i + 1) * b i| ≤ γ / 2

end KE02
