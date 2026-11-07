import KE02

open KE02

example (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hF : ConvexOn ℝ Set.univ F)
    (hs : ∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2)
    (hacc : ∀ q ∈ (alg2Run O n δ).state.log, |q.reply - F q.point| ≤ q.tol) :
    centeredVariation F (alg2Run O n δ).state.h (alg2Run O n δ).state.t < 1 / 2 :=
  (coreCertificate.algorithm2.run n δ F O hn hδ hF hs (by assumption)).centered_lt_half

example (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hF : ConvexOn ℝ Set.univ F)
    (hs : ∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) :
    centeredVariation F (alg2Run O n δ).state.h (alg2Run O n δ).state.t < 1 / 2 :=
  (coreCertificate.algorithm2.run n δ F O hn hδ hF hs (by assumption)).centered_lt_half
