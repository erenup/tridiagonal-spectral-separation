import KE02
import Mathlib.Analysis.Convex.Mul

/-!
Positive probes. Each statement must elaborate. They fix concrete values of
the definitions and prove that weakened premises or sharpened constants are
false, so the corresponding statements of the certificate are not vacuous.
-/

namespace KE02.Probes

open KE02

theorem threshold_one : alg2K 1 = 4 := by
  rw [alg2K, Nat.find_eq_iff]
  decide

theorem threshold_two : alg2K 2 = 7 := by
  rw [alg2K, Nat.find_eq_iff]
  decide

theorem threshold_ten : alg2K 10 = 14 := by
  rw [alg2K, Nat.find_eq_iff]
  decide

theorem doubling_two : doublingExponent 128 = 7 := by decide

theorem theta_two : alg2Theta 2 = 1 / 28 := by
  rw [alg2Theta, threshold_two]
  norm_num

theorem basic_threshold_two : basicK 2 = 12 := by
  rw [basicK, Nat.find_eq_iff]
  refine ⟨by norm_num, fun k hk => ?_⟩
  interval_cases k <;> norm_num

theorem tie_goes_left : selectCenter 1 0 0 0 = -1 := by
  norm_num [selectCenter]

theorem strict_goes_right : selectCenter 1 0 1 0 = 1 := by
  norm_num [selectCenter]

/-- The constant `4/3` of Lemma 4.1 cannot be lowered to `5/4`. -/
theorem weights_constant_sharp : ¬ ∀ t h x : ℝ, 0 < h →
    triangleWeight (t - h / 4) (h / 4) x + triangleWeight (t + h / 4) (h / 4) x ≤
      5 / 4 * triangleWeight t h x := by
  intro H
  have := H 0 1 (-1 / 4) one_pos
  norm_num [triangleWeight, abs_of_neg] at this

/-- Doubling the tolerance `2θh/256` breaks the error bound `1/64`. -/
theorem tolerance_sharp : ¬ ∀ (F : ℝ → ℝ) (θ h c v₀ v₁ v₂ v₃ : ℝ), 0 < θ → 0 < h →
    |v₀ - F (c - h)| ≤ 2 * (2 * θ * h / 256) →
    |v₁ - F (c - (1 - 2 * θ) * h)| ≤ 2 * (2 * θ * h / 256) →
    |v₂ - F (c + (1 - 2 * θ) * h)| ≤ 2 * (2 * θ * h / 256) →
    |v₃ - F (c + h)| ≤ 2 * (2 * θ * h / 256) →
    |endpointEstimate θ h v₀ v₁ v₂ v₃ - endpointVariation F θ h c| ≤ 1 / 64 := by
  intro H
  have := H (fun _ => 0) (1 / 4) 1 0 (1 / 256) (-1 / 256) (-1 / 256) (1 / 256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [endpointEstimate, endpointVariation] at this

/-- Inequality (34) fails for `θ = 1`. -/
theorem endpoint_control_needs_theta : ¬ ∀ (F : ℝ → ℝ) (θ h t : ℝ), ConvexOn ℝ Set.univ F →
    0 < θ → θ ≤ 1 → 0 < h → centeredVariation F h t ≤ endpointVariation F θ h t := by
  intro H
  have := H (fun x => x ^ 2) 1 1 0 (Even.convexOn_pow (by decide)) one_pos le_rfl one_pos
  norm_num [centeredVariation, endpointVariation] at this

/-- Bernoulli's bound `1/2` cannot be raised to `3/4`. -/
theorem bernoulli_sharp : ¬ ∀ K : ℕ, 1 ≤ K → (3 / 4 : ℝ) ≤ (1 - 1 / (2 * (K : ℝ))) ^ K := by
  intro H
  have := H 1 le_rfl
  norm_num at this

/-- The function used below: slopes `3` and `6`, a corner at `1/16`. -/
noncomputable def corner (x : ℝ) : ℝ := 3 * x + 3 * max (x - 1 / 16) 0

theorem corner_convex : ConvexOn ℝ Set.univ corner := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [corner, smul_eq_mul]
  have key : max (a * x + b * y - 1 / 16) 0 ≤ a * max (x - 1 / 16) 0 + b * max (y - 1 / 16) 0 := by
    apply max_le
    · have h₁ := mul_le_mul_of_nonneg_left (le_max_left (x - 1 / 16) 0) ha
      have h₂ := mul_le_mul_of_nonneg_left (le_max_left (y - 1 / 16) 0) hb
      linarith
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  linarith

theorem corner_slopes : ∀ u v : ℝ, u < v →
    ((2 : ℕ) : ℝ) * ((2 : ℕ) + 1) / 2 ≤ secant corner u v ∧
      secant corner u v ≤ ((2 : ℕ) : ℝ) ^ 2 * ((2 : ℕ) + 1) / 2 := by
  intro u v huv
  have hd : 0 < v - u := by linarith
  unfold secant corner
  push_cast
  rw [le_div_iff₀ hd, div_le_iff₀ hd]
  rcases le_total (u - 1 / 16) 0 with h₁ | h₁ <;> rcases le_total (v - 1 / 16) 0 with h₂ | h₂
  · rw [max_eq_right h₁, max_eq_right h₂]; constructor <;> linarith
  · rw [max_eq_right h₁, max_eq_left h₂]; constructor <;> linarith
  · rw [max_eq_left h₁, max_eq_right h₂]; constructor <;> linarith
  · rw [max_eq_left h₁, max_eq_left h₂]; constructor <;> linarith

/-- The accuracy premise of Theorem 4.2 cannot be dropped: with `n = 2`,
`δ = 1/4` and an oracle that always replies `0`, Algorithm 2 returns at
once, and the returned window has `S_h(t) = 3`. -/
theorem accuracy_premise_needed : ¬ ∀ (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle), 1 ≤ n → 0 < δ →
    ConvexOn ℝ Set.univ F →
    (∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) →
    centeredVariation F (alg2Run O n δ).state.h (alg2Run O n δ).state.t < 1 / 2 := by
  intro H
  have h := H 2 (1 / 4) corner (fun _ _ _ => 0) (by norm_num) (by norm_num) corner_convex
    corner_slopes
  have hrun : (alg2Run (fun _ _ _ => 0) 2 (1 / 4)).state = alg2Init (fun _ _ _ => 0) 2 (1 / 4) := by
    unfold alg2Run
    rw [threshold_two]
    have hstop : alg2Stops (alg2Init (fun _ _ _ => 0) 2 (1 / 4)) := by
      norm_num [alg2Stops, alg2Init, centeredEstimate]
    show (alg2Loop _ _ (6 + 1) 0 _).state = _
    simp only [alg2Loop, hstop, ↓reduceIte]
  rw [hrun] at h
  norm_num [alg2Init, centeredVariation, corner] at h

/-- A run that refines: for the corner function with exact replies, `n = 2`
and `δ = 1/4`, the initial test sees `Ŝ_h(t) = S_h(t) = 3`, so Algorithm 2
performs at least one refinement; all premises of the run theorem hold, so
its conclusions apply to this run. -/
theorem refining_run :
    1 ≤ (alg2Run (fun _ x _ => corner x) 2 (1 / 4)).refinements ∧
      Algorithm2Outcome 2 (1 / 4) corner (fun _ x _ => corner x)
        (alg2Run (fun _ x _ => corner x) 2 (1 / 4)) := by
  have hacc : ∀ q ∈ (alg2Run (fun _ x _ => corner x) 2 (1 / 4)).state.log,
      |q.reply - corner q.point| ≤ q.tol := by
    obtain ⟨hJK, hstate, -⟩ := run_spec (fun _ x _ => corner x) (n := 2) (δ := 1 / 4)
    intro q hq
    rw [hstate] at hq
    have htol := (state_queries (fun _ x _ => corner x) (n := 2) (δ := 1 / 4) (by norm_num)
      (by norm_num) _ hJK q hq).2.2
    rw [threshold_two] at htol
    have hpos : (0 : ℝ) < 1 / 4 / (2 ^ 16 * ((7 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ 4) := by positivity
    rw [exact_oracle_log corner 2 (1 / 4) _ q hq, sub_self, abs_zero]
    linarith
  have hout := coreCertificate.algorithm2.run 2 (1 / 4) corner (fun _ x _ => corner x)
    (by norm_num) (by norm_num) corner_convex corner_slopes hacc
  refine ⟨?_, hout⟩
  by_contra h
  have h0 : (alg2Run (fun _ x _ => corner x) 2 (1 / 4)).refinements = 0 := by omega
  have hpass := hout.returned_test_passes
  rw [hout.state_eq, h0] at hpass
  norm_num [alg2Stops, alg2State, alg2Init, centeredEstimate, corner] at hpass

end KE02.Probes
