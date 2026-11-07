import KE02.Algorithm2Definitions
import Mathlib.Analysis.Convex.Function

/-!
# Statements: inequality (34) and Lemma 4.2

`F : ℝ → ℝ` is an arbitrary convex function (Lemma 2.1 proves convexity of
the spectral function; here convexity is a premise). The radius of the two
candidate windows is `h' = (1/2 - θ) h`.
-/

namespace KE02

/-- Inequality (34), the nonnegativity of (13) and (33) for convex `F`, and
Lemma 4.2 with its proof ingredients, for every `0 < θ ≤ 1/4`. -/
structure EndpointCertificate : Prop where
  /-- (13): `S_h(t) ≥ 0` for convex `F`. -/
  centered_nonneg : ∀ (F : ℝ → ℝ) (h t : ℝ), ConvexOn ℝ Set.univ F → 0 < h →
    0 ≤ centeredVariation F h t
  /-- (33) is nonnegative by convexity. -/
  endpoint_nonneg : ∀ (F : ℝ → ℝ) (θ h t : ℝ), ConvexOn ℝ Set.univ F →
    0 < θ → θ ≤ 1 / 2 → 0 < h → 0 ≤ endpointVariation F θ h t
  /-- (34): `S_h(t) ≤ S_h^(θ)(t)` for `0 < θ ≤ 1/2`. -/
  centered_le_endpoint : ∀ (F : ℝ → ℝ) (θ h t : ℝ), ConvexOn ℝ Set.univ F →
    0 < θ → θ ≤ 1 / 2 → 0 < h → centeredVariation F h t ≤ endpointVariation F θ h t
  /-- The candidate windows `[t-h'-h', t-h'+h']` and `[t+h'-h', t+h'+h']`
  are `I_L = [t-(1-2θ)h, t]` and `I_R = [t, t+(1-2θ)h]`. -/
  child_windows : ∀ θ h t : ℝ,
    (t - (1 / 2 - θ) * h) - (1 / 2 - θ) * h = t - (1 - 2 * θ) * h ∧
    (t - (1 / 2 - θ) * h) + (1 / 2 - θ) * h = t ∧
    (t + (1 / 2 - θ) * h) - (1 / 2 - θ) * h = t ∧
    (t + (1 / 2 - θ) * h) + (1 / 2 - θ) * h = t + (1 - 2 * θ) * h
  /-- The seven requested points lie in the parent window `[t-h, t+h]`. -/
  points_in_parent : ∀ θ h t : ℝ, 0 < θ → θ ≤ 1 / 4 → 0 < h → ∀ i : Fin 7,
    t - h ≤ refinePoint θ ((1 / 2 - θ) * h) t i ∧ refinePoint θ ((1 / 2 - θ) * h) t i ≤ t + h
  /-- The seven points are exactly the four points of each child variation. -/
  points_of_children : ∀ (F : ℝ → ℝ) (θ h t : ℝ),
    endpointVariation F θ h (t - h) =
      endpointEstimate θ h (F (refinePoint θ h t 0)) (F (refinePoint θ h t 1))
        (F (refinePoint θ h t 2)) (F (refinePoint θ h t 3)) ∧
    endpointVariation F θ h (t + h) =
      endpointEstimate θ h (F (refinePoint θ h t 3)) (F (refinePoint θ h t 4))
        (F (refinePoint θ h t 5)) (F (refinePoint θ h t 6))
  /-- Proof of Lemma 4.2: the two child variations sum to at most the parent. -/
  children_sum : ∀ (F : ℝ → ℝ) (θ h t : ℝ), ConvexOn ℝ Set.univ F →
    0 < θ → θ ≤ 1 / 4 → 0 < h →
    endpointVariation F θ ((1 / 2 - θ) * h) (t - (1 / 2 - θ) * h) +
      endpointVariation F θ ((1 / 2 - θ) * h) (t + (1 / 2 - θ) * h) ≤
        endpointVariation F θ h t
  /-- (35). -/
  contraction : ∀ (F : ℝ → ℝ) (θ h t : ℝ), ConvexOn ℝ Set.univ F →
    0 < θ → θ ≤ 1 / 4 → 0 < h →
    min (endpointVariation F θ ((1 / 2 - θ) * h) (t - (1 / 2 - θ) * h))
        (endpointVariation F θ ((1 / 2 - θ) * h) (t + (1 / 2 - θ) * h)) ≤
      1 / 2 * endpointVariation F θ h t
  /-- Four values within `2θh/256` give `Ŝ_h^(θ)(c)` within `1/64`. -/
  estimate_error : ∀ (F : ℝ → ℝ) (θ h c v₀ v₁ v₂ v₃ : ℝ), 0 < θ → 0 < h →
    |v₀ - F (c - h)| ≤ 2 * θ * h / 256 →
    |v₁ - F (c - (1 - 2 * θ) * h)| ≤ 2 * θ * h / 256 →
    |v₂ - F (c + (1 - 2 * θ) * h)| ≤ 2 * θ * h / 256 →
    |v₃ - F (c + h)| ≤ 2 * θ * h / 256 →
    |endpointEstimate θ h v₀ v₁ v₂ v₃ - endpointVariation F θ h c| ≤ 1 / 64
  /-- Ties go left. -/
  ties_left : ∀ h t e : ℝ, selectCenter h t e e = t - h
  /-- (36) for one refinement: with the seven actual replies within
  `2θh'/256` of `F`, the center selected from the computed estimates
  satisfies `S_{h'}^(θ)(selected) ≤ S_h^(θ)(t)/2 + 1/32`. -/
  potential_step : ∀ (F : ℝ → ℝ) (θ h t : ℝ) (v : Fin 7 → ℝ),
    ConvexOn ℝ Set.univ F → 0 < θ → θ ≤ 1 / 4 → 0 < h →
    (∀ i : Fin 7, |v i - F (refinePoint θ ((1 / 2 - θ) * h) t i)| ≤
      2 * θ * ((1 / 2 - θ) * h) / 256) →
    endpointVariation F θ ((1 / 2 - θ) * h)
        (selectCenter ((1 / 2 - θ) * h) t
          (endpointEstimate θ ((1 / 2 - θ) * h) (v 0) (v 1) (v 2) (v 3))
          (endpointEstimate θ ((1 / 2 - θ) * h) (v 3) (v 4) (v 5) (v 6))) ≤
      1 / 2 * endpointVariation F θ h t + 1 / 32

end KE02
