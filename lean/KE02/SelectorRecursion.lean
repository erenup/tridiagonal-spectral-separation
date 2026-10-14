import KE02.SelectorGeometry

namespace KE02

@[simp] theorem selector_interval_zero (n : ℕ) (δ : ℝ) (replies : SelectorReplies) :
    selectorIntervalAt n δ replies 0 = selectorInitial n δ := rfl

@[simp] theorem selector_interval_succ (n : ℕ) (δ : ℝ) (replies : SelectorReplies) (j : ℕ) :
    selectorIntervalAt n δ replies (j + 1) =
      selectorStep (selectorIntervalAt n δ replies j) (replies j) := rfl

theorem selector_step_cases (I : SelectorInterval) (values : Bool → Fin 4 → ℝ) :
    selectorStep I values = selectorChild I false ∨
      selectorStep I values = selectorChild I true := by
  unfold selectorStep
  split_ifs <;> simp

theorem selector_interval_invariant (n : ℕ) (δ : ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (j : ℕ) :
    (selectorIntervalAt n δ replies j).left < (selectorIntervalAt n δ replies j).right ∧
    0 ≤ (selectorIntervalAt n δ replies j).left ∧
      (selectorIntervalAt n δ replies j).right ≤ δ / n := by
  induction j with
  | zero =>
      simp only [selector_interval_zero, selectorInitial]
      exact ⟨div_pos hδ (by exact_mod_cast hn), le_rfl, le_rfl⟩
  | succ j ih =>
      rw [selector_interval_succ]
      have hchild (side : Bool) :
          (selectorChild (selectorIntervalAt n δ replies j) side).left <
            (selectorChild (selectorIntervalAt n δ replies j) side).right ∧
          0 ≤ (selectorChild (selectorIntervalAt n δ replies j) side).left ∧
            (selectorChild (selectorIntervalAt n δ replies j) side).right ≤ δ / n := by
        have hnested := selector_child_nested ih.1 side
        exact ⟨selector_child_positive ih.1 side, ih.2.1.trans hnested.1,
          hnested.2.trans ih.2.2⟩
      rcases selector_step_cases (selectorIntervalAt n δ replies j) (replies j) with h | h
      · rw [h]; exact hchild false
      · rw [h]; exact hchild true

theorem selector_interval_nested (n : ℕ) (δ : ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (j : ℕ) :
    (selectorIntervalAt n δ replies j).left ≤ (selectorIntervalAt n δ replies (j+1)).left ∧
      (selectorIntervalAt n δ replies (j+1)).right ≤ (selectorIntervalAt n δ replies j).right := by
  rw [selector_interval_succ]
  rcases selector_step_cases (selectorIntervalAt n δ replies j) (replies j) with h | h
  all_goals rw [h]; exact selector_child_nested (selector_interval_invariant n δ replies hn hδ j).1 _

theorem selector_interval_length (n : ℕ) (δ : ℝ) (replies : SelectorReplies) (j : ℕ) :
    selectorLength (selectorIntervalAt n δ replies j) = δ / ((n : ℝ) * 4 ^ j) := by
  induction j with
  | zero => simp [selectorInitial, selectorLength]
  | succ j ih =>
      have hstep : selectorLength (selectorIntervalAt n δ replies (j+1)) =
          selectorLength (selectorIntervalAt n δ replies j) / 4 := by
        rw [selector_interval_succ]
        rcases selector_step_cases (selectorIntervalAt n δ replies j) (replies j) with h | h
        all_goals rw [h, selector_length_child]
      rw [hstep, ih, div_div, pow_succ]
      congr 1
      ring

theorem selector_query_contained (n : ℕ) (δ : ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (j : ℕ) (side : Bool) (q : Fin 4) :
    selectorQueryPoint (selectorChild (selectorIntervalAt n δ replies j) side) q ∈
      Set.Icc 0 (δ / n) := by
  have hi := selector_interval_invariant n δ replies hn hδ j
  have hc := selector_child_nested hi.1 side
  have hq := selector_query_within (selector_child_positive hi.1 side) q
  exact ⟨hi.2.1.trans (hc.1.trans hq.1), hq.2.trans (hc.2.trans hi.2.2)⟩

theorem selector_query_tolerance_positive (n : ℕ) (δ : ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (j : ℕ) (side : Bool) :
    0 < selectorTolerance (selectorChild (selectorIntervalAt n δ replies j) side) := by
  apply div_pos
  · exact selector_length_pos (selector_child_positive
      (selector_interval_invariant n δ replies hn hδ j).1 side)
  · norm_num

theorem selector_calls_count (n : ℕ) (δ : ℝ) (replies : SelectorReplies) (j : ℕ) :
    (selectorRun n δ replies j).calls.length = 8 * j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [selectorRun, selectorRoundCalls, ih]; omega

theorem selector_choice_left (n : ℕ) (δ : ℝ) (replies : SelectorReplies) (j : ℕ)
    (h : selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) false) (replies j false) ≤
      selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) true) (replies j true)) :
    selectorIntervalAt n δ replies (j+1) = selectorChild (selectorIntervalAt n δ replies j) false := by
  rw [selector_interval_succ]
  exact if_pos h

theorem selector_choice_right (n : ℕ) (δ : ℝ) (replies : SelectorReplies) (j : ℕ)
    (h : selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) true) (replies j true) <
      selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) false) (replies j false)) :
    selectorIntervalAt n δ replies (j+1) = selectorChild (selectorIntervalAt n δ replies j) true := by
  rw [selector_interval_succ]
  exact if_neg (not_le.mpr h)

theorem selector_transcript_valid (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (herror : SelectorReplyContract n δ F replies) :
    ∀ j ≤ selectorK n, ∀ call ∈ (selectorRun n δ replies j).calls,
      call.point ∈ Set.Icc 0 (δ / n) ∧ 0 < call.tolerance ∧
        |call.value - F call.point| ≤ call.tolerance := by
  intro j
  induction j with
  | zero => simp [selectorRun]
  | succ j ih =>
      intro hj call hmem
      have hjK : j < selectorK n := by omega
      have valid (side : Bool) (q : Fin 4) :
          let call := selectorCall (selectorChild (selectorIntervalAt n δ replies j) side) (replies j side) q
          call.point ∈ Set.Icc 0 (δ / n) ∧ 0 < call.tolerance ∧
            |call.value - F call.point| ≤ call.tolerance := by
        exact ⟨selector_query_contained n δ replies hn hδ j side q,
          selector_query_tolerance_positive n δ replies hn hδ j side, herror j hjK side q⟩
      change call ∈ (selectorRun n δ replies j).calls ++
        selectorRoundCalls (selectorIntervalAt n δ replies j) (replies j) at hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · exact ih (by omega) call hold
      · unfold selectorRoundCalls at hnew
        rcases List.mem_append.mp hnew with hleft | hright
        · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hleft
          exact valid false q
        · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hright
          exact valid true q

theorem selector_estimate_accuracy (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (herror : SelectorReplyContract n δ F replies)
    (j : ℕ) (hj : j < selectorK n) (side : Bool) :
    |selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) side) (replies j side) -
      selectorPotential F (selectorChild (selectorIntervalAt n δ replies j) side)| ≤ 1 / 64 := by
  exact selector_estimate_error (selector_child_positive
    (selector_interval_invariant n δ replies hn hδ j).1 side) F (replies j side) (herror j hj side)

theorem selector_potential_step (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (hF : ConvexOn ℝ (Set.Icc 0 (δ/n)) F)
    (herror : SelectorReplyContract n δ F replies) (j : ℕ) (hj : j < selectorK n) :
    selectorPotential F (selectorIntervalAt n δ replies (j+1)) ≤
      selectorPotential F (selectorIntervalAt n δ replies j) / 2 + 1/32 := by
  have hi := selector_interval_invariant n δ replies hn hδ j
  have hsum := selector_children_sum hF hi.1 hi.2.1 hi.2.2
  have hleft := abs_le.mp (selector_estimate_accuracy n δ F replies hn hδ herror j hj false)
  have hright := abs_le.mp (selector_estimate_accuracy n δ F replies hn hδ herror j hj true)
  by_cases hcmp : selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) false) (replies j false) ≤
      selectorEstimate (selectorChild (selectorIntervalAt n δ replies j) true) (replies j true)
  · rw [selector_choice_left n δ replies j hcmp]
    linarith
  · rw [selector_choice_right n δ replies j (lt_of_not_ge hcmp)]
    linarith

theorem selector_potential_iterated (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (replies : SelectorReplies)
    (hn : 0 < n) (hδ : 0 < δ) (hF : ConvexOn ℝ (Set.Icc 0 (δ/n)) F)
    (herror : SelectorReplyContract n δ F replies) :
    ∀ j ≤ selectorK n, selectorPotential F (selectorIntervalAt n δ replies j) ≤
      ((2 : ℝ)^j)⁻¹ * selectorPotential F (selectorInitial n δ) +
        (1/16) * (1 - ((2 : ℝ)^j)⁻¹) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hj
      have hstep := selector_potential_step n δ F replies hn hδ hF herror j (by omega)
      have hprev := ih (by omega)
      calc
        _ ≤ selectorPotential F (selectorIntervalAt n δ replies j) / 2 + 1/32 := hstep
        _ ≤ (((2:ℝ)^j)⁻¹ * selectorPotential F (selectorInitial n δ) +
              (1/16)*(1-((2:ℝ)^j)⁻¹)) / 2 + 1/32 := by linarith
        _ = _ := by rw [pow_succ, mul_inv_rev]; ring

end KE02
