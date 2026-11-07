import KE02.GraeffeDefinitions
import Mathlib.Data.Finset.Powerset

namespace KE02

open Polynomial

/-- The actual monic polynomial after the roots have been raised to `2 ^ k`. -/
noncomputable def poweredRootPolynomial {n : ℕ} (r : Fin n → ℝ) (k : ℕ) : ℝ[X] :=
  rootPolynomial (fun i => r i ^ (2 ^ k))

/-- The coefficient in descending degree order, defined from the polynomial product. -/
noncomputable def elementaryCoeff {n : ℕ} (r : Fin n → ℝ) (k j : ℕ) : ℝ :=
  (poweredRootPolynomial r k).coeff (n - j)

/-- The product of the first `j` powered roots; statements use `j ≤ n`. -/
noncomputable def leadingRootProduct {n : ℕ} (r : Fin n → ℝ) (k j : ℕ) : ℝ :=
  ∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < j), r i ^ (2 ^ k)

end KE02
