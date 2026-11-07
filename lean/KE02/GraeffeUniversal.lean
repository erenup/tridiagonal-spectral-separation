import KE02.GraeffeSplit
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace KE02

open Polynomial

/-- Substitution of the negative square is injective on real polynomials. -/
theorem comp_neg_sq_injective :
    Function.Injective (fun p : ℝ[X] => p.comp (-(X ^ 2))) := by
  intro p q h
  have h' : Polynomial.expand ℝ 2 (p.comp (-X)) =
      Polynomial.expand ℝ 2 (q.comp (-X)) := by
    simpa only [Polynomial.expand_eq_comp_X_pow, Polynomial.comp_assoc,
      Polynomial.neg_comp, Polynomial.X_comp] using h
  have hn := Polynomial.expand_injective (by decide : 0 < 2) h'
  have hb := congrArg (fun f : ℝ[X] => f.comp (-X)) hn
  simpa only [Polynomial.comp_neg_X_comp_neg_X] using hb

/-- The coefficient transform has the usual polynomial norm identity. -/
theorem graeffe_comp_neg_sq (p : ℝ[X]) :
    (graeffe p).comp (-(X ^ 2)) = p * p.comp (-X) := by
  have hn : p.comp (-X) = (evenPart p).comp (X ^ 2) +
      (-X) * ((oddPart p).comp (X ^ 2)) := by
    have h := congrArg (fun f : ℝ[X] => f.comp (-X)) (graeffe_reconstruct p)
    simpa only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.X_comp,
      Polynomial.comp_assoc, Polynomial.pow_comp, neg_sq] using h
  calc
    (graeffe p).comp (-(X ^ 2)) =
        ((evenPart p).comp (X ^ 2) + X * ((oddPart p).comp (X ^ 2))) *
        ((evenPart p).comp (X ^ 2) + (-X) * ((oddPart p).comp (X ^ 2))) := by
      simp only [graeffe, Polynomial.add_comp, Polynomial.pow_comp,
        Polynomial.mul_comp, Polynomial.comp_assoc, Polynomial.neg_comp,
        Polynomial.X_comp, neg_neg]
      ring
    _ = p * p.comp (-X) :=
      congrArg₂ (fun f g : ℝ[X] => f * g) (graeffe_reconstruct p).symm hn.symm

/-- One coefficient-defined Graeffe step squares every negated real root. -/
theorem graeffe_rootPolynomial (n : ℕ) (r : Fin n → ℝ) :
    graeffe (rootPolynomial r) = rootPolynomial (fun i => r i ^ 2) := by
  apply comp_neg_sq_injective
  change (graeffe (rootPolynomial r)).comp (-(X ^ 2)) =
    (rootPolynomial (fun i => r i ^ 2)).comp (-(X ^ 2))
  rw [graeffe_comp_neg_sq]
  simp only [rootPolynomial, Polynomial.prod_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]
  ring

/-- Every natural iterate squares the root exponents once more. -/
theorem graeffeIterate_rootPolynomial (n : ℕ) (r : Fin n → ℝ) (k : ℕ) :
    graeffeIterate k (rootPolynomial r) = rootPolynomial (fun i => r i ^ (2 ^ k)) := by
  induction k with
  | zero => simp [graeffeIterate]
  | succ k ih =>
    rw [graeffeIterate, ih, graeffe_rootPolynomial]
    congr 1
    funext i
    rw [← pow_mul, pow_succ]

/-- Complete universal Graeffe contract at the frozen definitions. -/
theorem graeffeCertificate : GraeffeCertificate where
  even_coeff := evenPart_coeff
  odd_coeff := oddPart_coeff
  reconstruct := graeffe_reconstruct
  one_step := graeffe_rootPolynomial
  iterate := graeffeIterate_rootPolynomial

end KE02
