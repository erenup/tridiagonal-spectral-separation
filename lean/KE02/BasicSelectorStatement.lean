import KE02.BasicSelectorDefinitions
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Statement: Lemma 4.1 and the constants of Theorem 4.1 and Remark 4.1

The transcript of Algorithm 1 is not formalized; one refinement with the
actual replies is (inequality (30) for a single step), together with the
scalar recursion and constants of the proof of Theorem 4.1.
-/

namespace KE02

structure BasicSelectorCertificate : Prop where
  /-- Proof of Lemma 4.1: `w_(t-h/4,h/4) + w_(t+h/4,h/4) ≤ (4/3) w_(t,h)` pointwise. -/
  weights : ∀ t h x : ℝ, 0 < h →
    triangleWeight (t - h / 4) (h / 4) x + triangleWeight (t + h / 4) (h / 4) x ≤
      4 / 3 * triangleWeight t h x
  /-- Equality at `x = t - h/4`, so `4/3` cannot be lowered. -/
  weights_attained : ∀ t h : ℝ, 0 < h →
    triangleWeight (t - h / 4) (h / 4) (t - h / 4) + triangleWeight (t + h / 4) (h / 4) (t - h / 4) =
      4 / 3 * triangleWeight t h (t - h / 4)
  /-- The sum form in the proof of Lemma 4.1, for every convex `F`. -/
  children_sum : ∀ (F : ℝ → ℝ) (h t : ℝ), ConvexOn ℝ Set.univ F → 0 < h →
    centeredVariation F (h / 4) (t - h / 4) + centeredVariation F (h / 4) (t + h / 4) ≤
      4 / 3 * centeredVariation F h t
  /-- (29). -/
  contraction : ∀ (F : ℝ → ℝ) (h t : ℝ), ConvexOn ℝ Set.univ F → 0 < h →
    min (centeredVariation F (h / 4) (t - h / 4)) (centeredVariation F (h / 4) (t + h / 4)) ≤
      2 / 3 * centeredVariation F h t
  /-- Three values within `r/256` give `Ŝ_r(c)` within `1/64`. -/
  estimate_error : ∀ (F : ℝ → ℝ) (r c lower middle upper : ℝ), 0 < r →
    |lower - F (c - r)| ≤ r / 256 → |middle - F c| ≤ r / 256 → |upper - F (c + r)| ≤ r / 256 →
    |centeredEstimate r lower middle upper - centeredVariation F r c| ≤ 1 / 64
  /-- (30) for one refinement: five actual replies within `(h/4)/256`, the
  smaller computed child variation (ties left) is selected. -/
  step : ∀ (F : ℝ → ℝ) (h t : ℝ) (v : Fin 5 → ℝ), ConvexOn ℝ Set.univ F → 0 < h →
    (∀ i : Fin 5, |v i - F (basicPoint (h / 4) t i)| ≤ h / 4 / 256) →
    centeredVariation F (h / 4)
        (selectCenter (h / 4) t (centeredEstimate (h / 4) (v 0) (v 1) (v 2))
          (centeredEstimate (h / 4) (v 2) (v 3) (v 4))) ≤
      2 / 3 * centeredVariation F h t + 1 / 32
  /-- Proof of Theorem 4.1: the secant bounds (9) give `S_h(t) < n³`. -/
  initial : ∀ (n : ℕ) (F : ℝ → ℝ) (h t : ℝ), 1 ≤ n → 0 < h →
    (∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) →
    centeredVariation F h t < (n : ℝ) ^ 3
  /-- `K_b` is the least natural number with `(3/2)^(K_b) ≥ 16 n³`, and
  `K_b = ⌈log_(3/2)(16 n³)⌉`. -/
  Kb_spec : ∀ n : ℕ, 16 * (n : ℝ) ^ 3 ≤ (3 / 2 : ℝ) ^ basicK n ∧
    ∀ k < basicK n, (3 / 2 : ℝ) ^ k < 16 * (n : ℝ) ^ 3
  Kb_ceil : ∀ n : ℕ, 1 ≤ n → basicK n = ⌈Real.logb (3 / 2) (16 * (n : ℝ) ^ 3)⌉₊
  /-- `(2/3)^(K_b) n³ ≤ 1/16`. -/
  first_term : ∀ n : ℕ, (2 / 3 : ℝ) ^ basicK n * (n : ℝ) ^ 3 ≤ 1 / 16
  /-- The iteration of (30) in the proof of Theorem 4.1. -/
  iterate : ∀ (n : ℕ) (s : ℕ → ℝ), s 0 < (n : ℝ) ^ 3 → (∀ j, s (j + 1) ≤ 2 / 3 * s j + 1 / 32) →
    ∀ j, s j < (2 / 3 : ℝ) ^ j * (n : ℝ) ^ 3 + 1 / 32 * ∑ l ∈ Finset.range j, (2 / 3 : ℝ) ^ l
  geometric : ∀ j : ℕ, 1 / 32 * ∑ l ∈ Finset.range j, (2 / 3 : ℝ) ^ l < 3 / 32
  /-- At `j = K_b` the variation is below `5/32`, and `5/32 + 2/64 < 1/2`. -/
  final : ∀ (n : ℕ) (s : ℕ → ℝ), s 0 < (n : ℝ) ^ 3 →
    (∀ j, s (j + 1) ≤ 2 / 3 * s j + 1 / 32) → s (basicK n) < 5 / 32
  stopping_constants : (5 : ℝ) / 32 + 2 / 64 < 1 / 2
  /-- `3 + 5 K_b` requests: three initial ones and five per refinement. -/
  calls : ∀ (n j : ℕ), j ≤ basicK n → 3 + 5 * j ≤ 3 + 5 * basicK n
  /-- Proof of Theorem 4.1: every radius satisfies `h ≤ δ/(2n) < 1` for
  `δ < 1/2`, as required by Proposition 3.1. -/
  radius_lt_one : ∀ (n : ℕ) (δ : ℝ), 1 ≤ n → 0 < δ → δ < 1 / 2 → ∀ j : ℕ,
    δ / (2 * n) / 4 ^ j ≤ δ / (2 * n) ∧ δ / (2 * n) < 1
  /-- (32): every radius `h_j = (δ/(2n)) 4^(-j)`, `j ≤ K_b`, exceeds
  `(δ/(8n)) (16 n³)^(-α)` with `α = log_(3/2) 4`. -/
  radius : ∀ (n : ℕ) (δ : ℝ), 1 ≤ n → 0 < δ → ∀ j ≤ basicK n,
    δ / (8 * n) * (16 * (n : ℝ) ^ 3) ^ (-Real.logb (3 / 2) 4) < δ / (2 * n) / 4 ^ j

end KE02
