import KE02.GraeffeStatement
import Mathlib.Tactic

namespace KE02

open Polynomial

theorem evenPart_coeff (p : ℝ[X]) (j : ℕ) :
    (evenPart p).coeff j = p.coeff (2 * j) := by
  simp [evenPart, Polynomial.coeff_contract, Nat.mul_comm]

theorem oddPart_coeff (p : ℝ[X]) (j : ℕ) :
    (oddPart p).coeff j = p.coeff (2 * j + 1) := by
  simp [oddPart, Polynomial.coeff_contract, Polynomial.coeff_divX, Nat.mul_comm]

theorem graeffe_reconstruct (p : ℝ[X]) :
    p = (evenPart p).comp (X ^ 2) + X * ((oddPart p).comp (X ^ 2)) := by
  change p = Polynomial.expand ℝ 2 (evenPart p) + X * Polynomial.expand ℝ 2 (oddPart p)
  ext j
  rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · cases k with
    | zero => simp [Polynomial.coeff_expand, evenPart_coeff]
    | succ k =>
      have h : ¬2 ∣ (2 * k + 1) := by omega
      have heq : k + 1 + (k + 1) = (2 * k + 1) + 1 := by omega
      rw [heq, Polynomial.coeff_add, Polynomial.coeff_X_mul]
      simp [Polynomial.coeff_expand, evenPart_coeff, h, show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  · have h : ¬2 ∣ (2 * k + 1) := by omega
    rw [Polynomial.coeff_add, Polynomial.coeff_X_mul]
    simp [Polynomial.coeff_expand, oddPart_coeff, h]

end KE02
