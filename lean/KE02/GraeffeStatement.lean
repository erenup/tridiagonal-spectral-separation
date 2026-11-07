import KE02.GraeffeDefinitions

namespace KE02

open Polynomial

/-- Universal coefficient and root identities for the actual Graeffe transform.
The root lists may contain arbitrary real numbers, including zero and repetitions.
The conclusions include every finite size and every natural iteration count. -/
structure GraeffeCertificate : Prop where
  even_coeff : ∀ (p : ℝ[X]) (j : ℕ), (evenPart p).coeff j = p.coeff (2 * j)
  odd_coeff : ∀ (p : ℝ[X]) (j : ℕ), (oddPart p).coeff j = p.coeff (2 * j + 1)
  reconstruct : ∀ p : ℝ[X],
    p = (evenPart p).comp (X ^ 2) + X * ((oddPart p).comp (X ^ 2))
  one_step : ∀ (n : ℕ) (r : Fin n → ℝ),
    graeffe (rootPolynomial r) = rootPolynomial (fun i => r i ^ 2)
  iterate : ∀ (n : ℕ) (r : Fin n → ℝ) (k : ℕ),
    graeffeIterate k (rootPolynomial r) = rootPolynomial (fun i => r i ^ (2 ^ k))

end KE02
