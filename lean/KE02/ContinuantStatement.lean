import KE02.ContinuantDefinitions

/-!
# Statement: the recurrence computes `det(zI + 2I + A)`
-/

namespace KE02

open Polynomial

structure ContinuantCertificate : Prop where
  /-- Expansion along the last row: the determinant of a tridiagonal matrix
  over any commutative ring `R : Type` is the continuant. -/
  det_tridiag : ∀ (R : Type) [CommRing R] (a b c : ℕ → R) (k : ℕ),
    (tridiag k a b c).det = continuant a b c k
  /-- Appendix A: for every real tridiagonal `A`, the recurrence ends in
  `det(zI + 2I + A)` as a polynomial in `z`. -/
  det_char : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j : Fin n, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → A i j = 0) →
    (Matrix.diagonal (fun _ => (X : ℝ[X])) + Matrix.diagonal (fun _ => (2 : ℝ[X])) +
      A.map C).det = charRecurrence A n
  /-- For symmetric `A`, `c_i = A_(i,i+1)²`. -/
  symmetric_coeff : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.transpose = A →
    ∀ i : ℕ, superEntry A i * subEntry A i = superEntry A i ^ 2

end KE02
