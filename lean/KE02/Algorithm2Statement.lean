import KE02.Algorithm2Definitions
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Statement: the scalar contract of Algorithm 2 and Theorem 4.2

The run is the actual transcript `alg2Run O n δ` for an arbitrary oracle
`O`. The premises on `F` are convexity on `ℝ` and the secant bounds (9);
in the paper both come from Lemma 2.1 for the spectral function. The only
premise on the replies is the absolute-error bound of every request that
the run actually made.
-/

namespace KE02

/-- Everything proved about one run `r` of Algorithm 2, where `θ = 1/(4K)`,
`(t_j, h_j)` are the centers and radii after `j` refinements and `(t, h)` is
the returned pair. -/
structure Algorithm2Outcome (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle) (r : Alg2Result) :
    Prop where
  /-- The run executes a `return` statement after at most `K` refinements. -/
  returns : r.returned = true
  refinements_le : r.refinements ≤ alg2K n
  /-- It returns the state reached after its refinements, at the first
  successful test. -/
  state_eq : r.state = alg2State O n δ r.refinements
  earlier_tests_fail : ∀ j < r.refinements, ¬ alg2Stops (alg2State O n δ j)
  returned_test_passes : alg2Stops r.state
  /-- `h_j = (1/2 - θ)^j δ/(2n)`. -/
  radius_formula : ∀ j : ℕ,
    (alg2State O n δ j).h = (1 / 2 - alg2Theta n) ^ j * (δ / (2 * n))
  /-- Every window `[t_j - h_j, t_j + h_j]` lies in `[0, δ/n]` and in the
  previous window. -/
  windows_inside : ∀ j : ℕ, 0 ≤ (alg2State O n δ j).t - (alg2State O n δ j).h ∧
    (alg2State O n δ j).t + (alg2State O n δ j).h ≤ δ / n
  windows_nested : ∀ j : ℕ,
    (alg2State O n δ j).t - (alg2State O n δ j).h ≤
      (alg2State O n δ (j + 1)).t - (alg2State O n δ (j + 1)).h ∧
    (alg2State O n δ (j + 1)).t + (alg2State O n δ (j + 1)).h ≤
      (alg2State O n δ j).t + (alg2State O n δ j).h
  /-- The initial endpoint variation is below `n³` (from (9)). -/
  initial_potential :
    endpointVariation F (alg2Theta n) (alg2State O n δ 0).h (alg2State O n δ 0).t < (n : ℝ) ^ 3
  /-- (36) along the run. -/
  potential_step : ∀ j < r.refinements,
    endpointVariation F (alg2Theta n) (alg2State O n δ (j + 1)).h (alg2State O n δ (j + 1)).t ≤
      1 / 2 * endpointVariation F (alg2Theta n) (alg2State O n δ j).h (alg2State O n δ j).t +
        1 / 32
  /-- The iterated form used in the proof of Theorem 4.2. -/
  potential_bound : ∀ j ≤ r.refinements,
    endpointVariation F (alg2Theta n) (alg2State O n δ j).h (alg2State O n δ j).t ≤
      (1 / 2) ^ j *
          endpointVariation F (alg2Theta n) (alg2State O n δ 0).h (alg2State O n δ 0).t +
        1 / 32 * ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i
  /-- If all `K` refinements are performed, `S_(h_K)^(θ)(t_K) < 1/8`. -/
  potential_final : r.refinements = alg2K n →
    endpointVariation F (alg2Theta n) (alg2State O n δ r.refinements).h
      (alg2State O n δ r.refinements).t < 1 / 8
  /-- The computed `Ŝ_h(t)` of the returned test is within `1/64` of `S_h(t)`. -/
  estimate_accuracy : |r.state.estimate - centeredVariation F r.state.h r.state.t| ≤ 1 / 64
  /-- (37), first part: `S_h(t) < 1/2`. -/
  centered_lt_half : centeredVariation F r.state.h r.state.t < 1 / 2
  /-- (37), second part: `h > δ/(128 n⁴)`; also `h ≤ δ/(2n)`. -/
  radius_lower : δ / (128 * (n : ℝ) ^ 4) < r.state.h
  radius_upper : r.state.h ≤ δ / (2 * n)
  /-- The returned window lies in `[0, δ/n]`; hence `0 ≤ t` and `n t ≤ δ`. -/
  window : 0 ≤ r.state.t - r.state.h ∧ r.state.t + r.state.h ≤ δ / n
  budget : 0 ≤ r.state.t ∧ (n : ℝ) * r.state.t ≤ δ
  /-- Every request of the run lies in `[0, δ/n]` with a positive tolerance. -/
  queries_inside : ∀ q ∈ r.state.log, 0 ≤ q.point ∧ q.point ≤ δ / n ∧ 0 < q.tol
  /-- Every requested accuracy is at most `δ/(512 n)`; for `δ < 1/2` all are
  below `1` (the range `ε_min ≤ ε < 1` used in the proof of Theorem 1.1). -/
  tolerance_upper : ∀ q ∈ r.state.log, q.tol ≤ δ / (512 * n)
  tolerance_lt_one : δ < 1 / 2 → ∀ q ∈ r.state.log, q.tol < 1
  /-- `h ≤ δ/(2n) < 1` for `δ < 1/2`, as required by Proposition 3.1. -/
  radius_lt_one : δ < 1 / 2 → r.state.h < 1
  /-- Exactly `3 + 8j` requests after `j` refinements, hence at most `3 + 8K`. -/
  calls_exact : r.state.log.length = 3 + 8 * r.refinements
  calls_le : r.state.log.length ≤ 3 + 8 * alg2K n
  /-- The scalar inequality used for (38): `h²/(2²⁰ n⁴) > 2⁻³⁴ δ² n⁻¹²` (the gap bound
  (38) is not formalized). -/
  gap_scale : (2 : ℝ) ⁻¹ ^ 34 * δ ^ 2 / (n : ℝ) ^ 12 < r.state.h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)
  /-- (40): every requested accuracy exceeds `δ/(2¹⁶ K n⁴)`. -/
  min_accuracy : ∀ q ∈ r.state.log, δ / (2 ^ 16 * (alg2K n : ℝ) * (n : ℝ) ^ 4) < q.tol

/-- The scalar contract of Algorithm 2 (Theorem 4.2 without Proposition 3.1). -/
structure Algorithm2Certificate : Prop where
  /-- `K` is the least natural number with `16 n³ ≤ 2^K`. -/
  K_spec : ∀ n : ℕ, 16 * n ^ 3 ≤ 2 ^ alg2K n ∧ ∀ k < alg2K n, 2 ^ k < 16 * n ^ 3
  /-- Repeated doubling finds `K`. -/
  K_doubling : ∀ n : ℕ, doublingExponent (16 * n ^ 3) = alg2K n
  /-- `K = ⌈log₂(16 n³)⌉`. -/
  K_ceil_log : ∀ n : ℕ, 1 ≤ n → alg2K n = ⌈Real.logb 2 (16 * (n : ℝ) ^ 3)⌉₊
  /-- `2^K < 32 n³` and `K ≥ 1`. -/
  K_upper : ∀ n : ℕ, 1 ≤ n → 2 ^ alg2K n < 32 * n ^ 3 ∧ 1 ≤ alg2K n
  /-- `0 < θ ≤ 1/4` and `1/2 - θ = (1 - 1/(2K))/2`. -/
  theta_range : ∀ n : ℕ, 1 ≤ n → 0 < alg2Theta n ∧ alg2Theta n ≤ 1 / 4 ∧
    1 / 2 - alg2Theta n = 1 / 2 * (1 - 1 / (2 * (alg2K n : ℝ)))
  /-- Bernoulli's inequality as used: `(1 - 1/(2K))^K ≥ 1/2`. -/
  bernoulli : ∀ K : ℕ, 1 ≤ K → (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (K : ℝ))) ^ K
  /-- `L_K = (δ/n)(1/2 - θ)^K > δ/(64 n⁴)`. -/
  LK_bound : ∀ (n : ℕ) (δ : ℝ), 1 ≤ n → 0 < δ →
    δ / (64 * (n : ℝ) ^ 4) < δ / n * (1 / 2 - alg2Theta n) ^ alg2K n
  /-- The second inequality of (5): `2⁻³⁴ δ² n⁻¹² ≥ 2⁻³⁴ (δ/n)¹²` for `0 < δ < 1`. -/
  main_bound_form : ∀ (n : ℕ) (δ : ℝ), 1 ≤ n → 0 < δ → δ < 1 →
    (2 : ℝ)⁻¹ ^ 34 * (δ / n) ^ 12 ≤ (2 : ℝ)⁻¹ ^ 34 * δ ^ 2 / (n : ℝ) ^ 12
  /-- The stopping constants `1/8 + 1/128 + 1/64 < 1/2`. -/
  stopping_constants : (1 : ℝ) / 8 + 1 / 128 + 1 / 64 < 1 / 2
  /-- Three values within `2θh/256` give `Ŝ_h(c)` within `θ/32 ≤ 1/128`. -/
  midpoint_estimate_error : ∀ (F : ℝ → ℝ) (θ h c lower middle upper : ℝ), 0 < θ → θ ≤ 1 / 4 →
    0 < h → |lower - F (c - h)| ≤ 2 * θ * h / 256 → |middle - F c| ≤ 2 * θ * h / 256 →
    |upper - F (c + h)| ≤ 2 * θ * h / 256 →
    |centeredEstimate h lower middle upper - centeredVariation F h c| ≤ θ / 32 ∧ θ / 32 ≤ 1 / 128
  /-- The run of Algorithm 2 on any oracle whose replies to the requests of
  that run are within the requested absolute error. -/
  run : ∀ (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle), 1 ≤ n → 0 < δ →
    ConvexOn ℝ Set.univ F →
    (∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) →
    (∀ q ∈ (alg2Run O n δ).state.log, |q.reply - F q.point| ≤ q.tol) →
    Algorithm2Outcome n δ F O (alg2Run O n δ)
  /-- The premises of `run` are satisfiable for every `n ≥ 1` and `δ > 0`. -/
  premises_satisfiable : ∀ (n : ℕ) (δ : ℝ), 1 ≤ n → 0 < δ →
    ∃ (F : ℝ → ℝ) (O : Oracle), ConvexOn ℝ Set.univ F ∧
      (∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
        secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) ∧
      ∀ q ∈ (alg2Run O n δ).state.log, |q.reply - F q.point| ≤ q.tol

end KE02
