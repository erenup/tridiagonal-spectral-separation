import KE02.CoefficientStatement
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

namespace KE02

open Polynomial

/-- Vieta's formula identifies the actual descending coefficient with the subset sum. -/
theorem elementaryCoeff_expansion {n : ℕ} (r : Fin n → ℝ) (k j : ℕ) (hj : j ≤ n) :
    elementaryCoeff r k j =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        ∏ i ∈ s, r i ^ (2 ^ k) := by
  have hdegree : n - j ≤ (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_le n j
  unfold elementaryCoeff poweredRootPolynomial rootPolynomial
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.sub_sub_self hj] using
    Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin n))
      (fun i => r i ^ (2 ^ k)) hdegree

theorem elementaryCoeff_zero {n : ℕ} (r : Fin n → ℝ) (k : ℕ) :
    elementaryCoeff r k 0 = 1 := by
  rw [elementaryCoeff_expansion r k 0 (Nat.zero_le n)]
  simp

theorem elementaryCoeff_pos {n : ℕ} (r : Fin n → ℝ) (k j : ℕ)
    (hr : ∀ i, 0 < r i) (hj : j ≤ n) : 0 < elementaryCoeff r k j := by
  rw [elementaryCoeff_expansion r k j hj]
  apply Finset.sum_pos
  · intro s _
    exact Finset.prod_pos fun i _ => pow_pos (hr i) _
  · apply Finset.powersetCard_nonempty.mpr
    simpa using hj

end KE02
