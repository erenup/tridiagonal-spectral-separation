import Mathlib.Data.Real.Basic

/-!
# Slope variations of a real function

Literal definitions of the centered slope variation (13) and the endpoint
slope variation (33), together with the same formulas evaluated on
approximate function values (the computed quantities written with a hat in
the paper). Nothing here assumes convexity or any accuracy property.
-/

namespace KE02

/-- Secant slope of `F` over `[u, v]`. -/
noncomputable def secant (F : ℝ → ℝ) (u v : ℝ) : ℝ := (F v - F u) / (v - u)

/-- Equation (13): the centered slope variation `S_h(t)`. -/
noncomputable def centeredVariation (F : ℝ → ℝ) (h t : ℝ) : ℝ :=
  (F (t + h) - F t) / h - (F t - F (t - h)) / h

/-- Equation (33): the endpoint slope variation `S_h^(θ)(t)`, defined in the paper for
`0 < θ ≤ 1/2`; here `θ` is any real number and each statement carries its range. -/
noncomputable def endpointVariation (F : ℝ → ℝ) (θ h t : ℝ) : ℝ :=
  (F (t + h) - F (t + (1 - 2 * θ) * h)) / (2 * θ * h) -
    (F (t - (1 - 2 * θ) * h) - F (t - h)) / (2 * θ * h)

/-- The formula (13) evaluated on approximate values `lower ≈ F(t-h)`,
`middle ≈ F(t)` and `upper ≈ F(t+h)`. -/
noncomputable def centeredEstimate (h lower middle upper : ℝ) : ℝ :=
  (upper - middle) / h - (middle - lower) / h

/-- The formula (33) evaluated on approximate values `v₀ ≈ F(t-h)`,
`v₁ ≈ F(t-(1-2θ)h)`, `v₂ ≈ F(t+(1-2θ)h)` and `v₃ ≈ F(t+h)`. -/
noncomputable def endpointEstimate (θ h v₀ v₁ v₂ v₃ : ℝ) : ℝ :=
  (v₃ - v₂) / (2 * θ * h) - (v₁ - v₀) / (2 * θ * h)

end KE02
