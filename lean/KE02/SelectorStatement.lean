import KE02.SelectorDefinitions

namespace KE02

/-- The complete scalar-selector conclusion. Its function is an arbitrary real
convex function; spectral interpretation and oracle arithmetic cost are absent. -/
structure SelectorOutcome (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (replies : SelectorReplies) :
    Prop where
  threshold_reached : 16 * n ^ 3 ≤ 2 ^ selectorK n
  threshold_least : ∀ j < selectorK n, 2 ^ j < 16 * n ^ 3
  threshold_upper : 2 ^ selectorK n < 32 * n ^ 3
  interval_positive : ∀ j ≤ selectorK n,
    (selectorIntervalAt n δ replies j).left < (selectorIntervalAt n δ replies j).right
  interval_contained : ∀ j ≤ selectorK n,
    0 ≤ (selectorIntervalAt n δ replies j).left ∧
      (selectorIntervalAt n δ replies j).right ≤ δ / n
  interval_nested : ∀ j < selectorK n,
    (selectorIntervalAt n δ replies j).left ≤ (selectorIntervalAt n δ replies (j + 1)).left ∧
      (selectorIntervalAt n δ replies (j + 1)).right ≤ (selectorIntervalAt n δ replies j).right
  interval_length : ∀ j ≤ selectorK n,
    selectorLength (selectorIntervalAt n δ replies j) = δ / ((n : ℝ) * 4 ^ j)
  query_contained : ∀ j < selectorK n, ∀ side : Bool, ∀ q : Fin 4,
    selectorQueryPoint (selectorChild (selectorIntervalAt n δ replies j) side) q ∈
      Set.Icc 0 (δ / n)
  query_tolerance_positive : ∀ j < selectorK n, ∀ side : Bool,
    0 < selectorTolerance (selectorChild (selectorIntervalAt n δ replies j) side)
  query_accuracy : SelectorReplyContract n δ F replies
  transcript_valid : ∀ call ∈ (selectorRun n δ replies (selectorK n)).calls,
    call.point ∈ Set.Icc 0 (δ / n) ∧ 0 < call.tolerance ∧
      |call.value - F call.point| ≤ call.tolerance
  estimate_accuracy : ∀ j < selectorK n, ∀ side : Bool,
    |selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) side) (replies j side) -
      selectorPotential F (selectorChild (selectorIntervalAt n δ replies j) side)| ≤ 1 / 64
  children_sum : ∀ j < selectorK n,
    selectorPotential F (selectorChild (selectorIntervalAt n δ replies j) false) +
      selectorPotential F (selectorChild (selectorIntervalAt n δ replies j) true) ≤
        selectorPotential F (selectorIntervalAt n δ replies j)
  choice_left : ∀ j < selectorK n,
    selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) false) (replies j false) ≤
      selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) true) (replies j true) →
        selectorIntervalAt n δ replies (j + 1) =
          selectorChild (selectorIntervalAt n δ replies j) false
  choice_right : ∀ j < selectorK n,
    selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) true) (replies j true) <
      selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) false) (replies j false) →
        selectorIntervalAt n δ replies (j + 1) =
          selectorChild (selectorIntervalAt n δ replies j) true
  potential_nonnegative : ∀ j ≤ selectorK n,
    0 ≤ selectorPotential F (selectorIntervalAt n δ replies j)
  potential_step : ∀ j < selectorK n,
    selectorPotential F (selectorIntervalAt n δ replies (j + 1)) ≤
      selectorPotential F (selectorIntervalAt n δ replies j) / 2 + 1 / 32
  potential_iterated : ∀ j ≤ selectorK n,
    selectorPotential F (selectorIntervalAt n δ replies j) ≤
      ((2 : ℝ) ^ j)⁻¹ * selectorPotential F (selectorInitial n δ) +
        (1 / 16) * (1 - ((2 : ℝ) ^ j)⁻¹)
  calls_count : (selectorRun n δ replies (selectorK n)).calls.length = 8 * selectorK n
  final_contained :
    0 ≤ selectorCenter (selectorFinal n δ replies) - selectorRadius (selectorFinal n δ replies) ∧
    selectorCenter (selectorFinal n δ replies) - selectorRadius (selectorFinal n δ replies) <
      selectorCenter (selectorFinal n δ replies) + selectorRadius (selectorFinal n δ replies) ∧
    selectorCenter (selectorFinal n δ replies) + selectorRadius (selectorFinal n δ replies) ≤ δ / n
  radius_exact : selectorRadius (selectorFinal n δ replies) =
    δ / (4 * (n : ℝ) * 4 ^ selectorK n)
  radius_positive : 0 < selectorRadius (selectorFinal n δ replies)
  radius_lower : δ / (4096 * (n : ℝ) ^ 7) < selectorRadius (selectorFinal n δ replies)
  radius_lt_one : selectorRadius (selectorFinal n δ replies) < 1
  final_potential : selectorPotential F (selectorFinal n δ replies) < 1 / 8
  final_defect :
    F (selectorCenter (selectorFinal n δ replies) + selectorRadius (selectorFinal n δ replies)) +
      F (selectorCenter (selectorFinal n δ replies) - selectorRadius (selectorFinal n δ replies)) -
        2 * F (selectorCenter (selectorFinal n δ replies)) <
          selectorRadius (selectorFinal n δ replies) / 8

/-- The first scalar target quantifies over every n, δ, convex F and reply
stream satisfying precisely the stated initial-potential and absolute-error
premises. It contains no spectral or cost assumption. -/
structure SelectorCertificate : Prop where
  robust : ∀ (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (replies : SelectorReplies),
    2 ≤ n → 0 < δ → δ < 1 / 2 → ConvexOn ℝ (Set.Icc 0 (δ / n)) F →
      selectorPotential F (selectorInitial n δ) < (n : ℝ) ^ 3 →
        SelectorReplyContract n δ F replies → SelectorOutcome n δ F replies

end KE02
