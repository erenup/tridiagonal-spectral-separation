import KE02.SelectorRecursion
import KE02.SelectorBounds

namespace KE02

/-- The selector certificate uses the actual recursively chosen queries, arbitrary
independent replies within their absolute tolerances, and the prescribed left tie rule. -/
theorem selectorCertificate : SelectorCertificate := by
  refine ⟨?_⟩
  intro n δ F replies hn hδ hsmall hF hP0 herror
  have hnpos : 0 < n := by omega
  have hi := selector_interval_invariant n δ replies hnpos hδ
  have hfinal : (selectorFinal n δ replies).left < (selectorFinal n δ replies).right ∧
      0 ≤ (selectorFinal n δ replies).left ∧ (selectorFinal n δ replies).right ≤ δ/n :=
    hi (selectorK n)
  have hradius : selectorRadius (selectorFinal n δ replies) =
      δ / (4 * (n:ℝ) * 4^selectorK n) := by
    unfold selectorRadius selectorFinal
    rw [selector_interval_length, div_div]
    congr 1
    ring
  have hrpos : 0 < selectorRadius (selectorFinal n δ replies) :=
    div_pos (selector_length_pos hfinal.1) (by norm_num)
  have hcontained :
      0 ≤ selectorCenter (selectorFinal n δ replies) - selectorRadius (selectorFinal n δ replies) ∧
      selectorCenter (selectorFinal n δ replies) - selectorRadius (selectorFinal n δ replies) <
        selectorCenter (selectorFinal n δ replies) + selectorRadius (selectorFinal n δ replies) ∧
      selectorCenter (selectorFinal n δ replies) + selectorRadius (selectorFinal n δ replies) ≤ δ/n := by
    dsimp [selectorCenter, selectorRadius, selectorLength]
    constructor
    · linarith [hfinal.1, hfinal.2.1]
    · constructor <;> linarith [hfinal.1, hfinal.2.2]
  have hriter : ∀ j ≤ selectorK n,
      selectorPotential F (selectorIntervalAt n δ replies j) ≤
        ((2:ℝ)^j)⁻¹ * selectorPotential F (selectorInitial n δ) +
          (1/16) * (1-((2:ℝ)^j)⁻¹) :=
    selector_potential_iterated n δ F replies hnpos hδ hF herror
  have hpotential : selectorPotential F (selectorFinal n δ replies) < 1/8 :=
    selector_final_potential_bound n (selectorPotential F (selectorInitial n δ))
      (selectorPotential F (selectorFinal n δ replies)) hP0 (hriter (selectorK n) le_rfl)
  refine {
    threshold_reached := selector_threshold_reached n
    threshold_least := selector_threshold_least n
    threshold_upper := selector_threshold_upper n hn
    interval_positive := fun j _ => (hi j).1
    interval_contained := fun j _ => (hi j).2
    interval_nested := fun j _ => selector_interval_nested n δ replies hnpos hδ j
    interval_length := fun j _ => selector_interval_length n δ replies j
    query_contained := fun j _ side q => selector_query_contained n δ replies hnpos hδ j side q
    query_tolerance_positive := fun j _ side => selector_query_tolerance_positive n δ replies hnpos hδ j side
    query_accuracy := herror
    transcript_valid := selector_transcript_valid n δ F replies hnpos hδ herror (selectorK n) le_rfl
    estimate_accuracy := selector_estimate_accuracy n δ F replies hnpos hδ herror
    children_sum := fun j _ => selector_children_sum hF (hi j).1 (hi j).2.1 (hi j).2.2
    choice_left := fun j _ h => selector_choice_left n δ replies j h
    choice_right := fun j _ h => selector_choice_right n δ replies j h
    potential_nonnegative := fun j _ => selector_potential_nonnegative hF (hi j).1 (hi j).2.1 (hi j).2.2
    potential_step := selector_potential_step n δ F replies hnpos hδ hF herror
    potential_iterated := hriter
    calls_count := selector_calls_count n δ replies (selectorK n)
    final_contained := hcontained
    radius_exact := hradius
    radius_positive := hrpos
    radius_lower := ?_
    radius_lt_one := ?_
    final_potential := hpotential
    final_defect := ?_
  }
  · rw [hradius]
    exact selector_radius_lower_bound n δ hn hδ
  · have hnreal : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hquot : δ/n ≤ δ := div_le_self hδ.le hnreal
    dsimp [selectorRadius, selectorLength]
    linarith [hfinal.2.1, hfinal.2.2]
  · have hd := selector_defect_le hF hfinal.1 hfinal.2.1 hfinal.2.2
    have hp := mul_lt_mul_of_pos_left hpotential hrpos
    linarith

end KE02
