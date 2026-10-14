import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic

namespace KE02

open Polynomial

/-- The polynomial whose coefficient at `j` is the input coefficient at `2 * j`. -/
noncomputable def evenPart (p : ℝ[X]) : ℝ[X] :=
  Polynomial.contract 2 p

/-- The polynomial whose coefficient at `j` is the input coefficient at `2 * j + 1`. -/
noncomputable def oddPart (p : ℝ[X]) : ℝ[X] :=
  Polynomial.contract 2 p.divX

/-- The ordinary even/odd-coefficient Graeffe transform. -/
noncomputable def graeffe (p : ℝ[X]) : ℝ[X] :=
  ((evenPart p).comp (-X)) ^ 2 + X * (((oddPart p).comp (-X)) ^ 2)

/-- Repeated application of the coefficient-defined transform. -/
noncomputable def graeffeIterate : ℕ → ℝ[X] → ℝ[X]
  | 0, p => p
  | k + 1, p => graeffe (graeffeIterate k p)

/-- A monic polynomial specified by its negated real roots. -/
noncomputable def rootPolynomial {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  ∏ i : Fin n, (X + C (r i))

end KE02
