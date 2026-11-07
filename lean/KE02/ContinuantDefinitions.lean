import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# Appendix A: the tridiagonal determinant recurrence

`tridiag k a b c` is the `k × k` matrix with diagonal `a 0, …, a (k-1)`,
superdiagonal `b 0, …, b (k-2)` and subdiagonal `c 0, …, c (k-2)`. For a real
`n × n` matrix `A`, `charRecurrence A` is the recurrence of Appendix A for
`det(zI + 2I + A)`: with the paper's 1-based indices, `P_0 = 1`,
`P_1 = z + 2 + a_1`, `P_i = (z + 2 + a_i) P_(i-1) - c_(i-1) P_(i-2)` for
`2 ≤ i ≤ n`, where `a_i = A_(i,i)` and `c_i = A_(i,i+1) A_(i+1,i)` (which is
`|A_(i,i+1)|²` for symmetric `A`). The three cases of `charRecurrence` are
these three equations: `charRecurrence A (i + 2)` is `P_(i+2)`, with
`diagEntry A (i + 1) = a_(i+2)` and `superEntry A i * subEntry A i = c_(i+1)`.
Entry functions are `0`-based and vanish outside the matrix; the recurrence
is used at the index `n`, and only its terms with index at most `n` enter.
-/

noncomputable section

namespace KE02

open Polynomial

def tridiag {R : Type*} [CommRing R] (k : ℕ) (a b c : ℕ → R) : Matrix (Fin k) (Fin k) R :=
  fun i j => if (i : ℕ) = j then a i else if (j : ℕ) = i + 1 then b i
    else if (i : ℕ) = j + 1 then c j else 0

/-- `Q 0 = 1`, `Q 1 = a 0`, `Q (k+2) = a (k+1) Q (k+1) - b k c k Q k`. -/
def continuant {R : Type*} [CommRing R] (a b c : ℕ → R) : ℕ → R
  | 0 => 1
  | 1 => a 0
  | k + 2 => a (k + 1) * continuant a b c (k + 1) - b k * c k * continuant a b c k

/-- `A_(i,i)` (0-based). -/
def diagEntry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if h : i < n then A ⟨i, h⟩ ⟨i, h⟩ else 0

/-- `A_(i,i+1)` (0-based). -/
def superEntry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if h : i + 1 < n then A ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0

/-- `A_(i+1,i)` (0-based). -/
def subEntry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if h : i + 1 < n then A ⟨i + 1, h⟩ ⟨i, by omega⟩ else 0

/-- The recurrence of Appendix A, indexed by the size of the leading block. -/
def charRecurrence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + C (2 + diagEntry A 0)
  | i + 2 => (X + C (2 + diagEntry A (i + 1))) * charRecurrence A (i + 1) -
      C (superEntry A i * subEntry A i) * charRecurrence A i

end KE02
