import KE02.Algorithm2Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Section 4.1: the basic selector (Algorithm 1), single-round objects

The triangular weight of the proof of Lemma 4.1, the threshold `K_b`, and
the five evaluation points of one refinement of Algorithm 1.
-/

noncomputable section

namespace KE02

/-- `w_(t,h)(x) = (1 - |x - t|/h)_+`. -/
def triangleWeight (t h x : ℝ) : ℝ := max (1 - |x - t| / h) 0

theorem exists_three_halves_pow_ge (x : ℝ) : ∃ k : ℕ, x ≤ (3 / 2 : ℝ) ^ k :=
  (pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 3 / 2)).imp fun _ h => h.le

/-- `K_b`: the least natural number with `(3/2)^(K_b) ≥ 16 n³`. -/
def basicK (n : ℕ) : ℕ := Nat.find (exists_three_halves_pow_ge (16 * (n : ℝ) ^ 3))

/-- The five points `t-2h, t-h, t, t+h, t+2h` of one refinement of
Algorithm 1 with the updated radius `h`: indices 0–2 serve `Ŝ_h(t-h)` and
indices 2–4 serve `Ŝ_h(t+h)`. -/
def basicPoint (h t : ℝ) : Fin 5 → ℝ := ![(t - h) - h, t - h, t, t + h, (t + h) + h]

end KE02
