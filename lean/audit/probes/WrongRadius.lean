import KE02

open KE02

example (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hF : ConvexOn ℝ Set.univ F)
    (hs : ∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2)
    (hacc : ∀ q ∈ (alg2Run O n δ).state.log, |q.reply - F q.point| ≤ q.tol) :
    δ / (128 * (n : ℝ) ^ 4) < (alg2Run O n δ).state.h :=
  (coreCertificate.algorithm2.run n δ F O hn hδ hF hs hacc).radius_lower

example (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hF : ConvexOn ℝ Set.univ F)
    (hs : ∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2)
    (hacc : ∀ q ∈ (alg2Run O n δ).state.log, |q.reply - F q.point| ≤ q.tol) :
    δ / (64 * (n : ℝ) ^ 4) < (alg2Run O n δ).state.h :=
  (coreCertificate.algorithm2.run n δ F O hn hδ hF hs hacc).radius_lower
