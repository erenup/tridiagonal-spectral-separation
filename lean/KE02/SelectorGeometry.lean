import KE02.SelectorStatement
import Mathlib.Tactic

namespace KE02

theorem selector_length_pos {I : SelectorInterval} (h : I.left < I.right) :
    0 < selectorLength I := sub_pos.mpr h

@[simp] theorem selector_length_child (I : SelectorInterval) (side : Bool) :
    selectorLength (selectorChild I side) = selectorLength I / 4 := by
  cases side <;> simp [selectorChild, selectorLength] <;> ring

theorem selector_child_positive {I : SelectorInterval} (h : I.left < I.right)
    (side : Bool) : (selectorChild I side).left < (selectorChild I side).right := by
  have hp := selector_length_pos h
  have : 0 < selectorLength (selectorChild I side) := by
    rw [selector_length_child]
    positivity
  exact sub_pos.mp this

theorem selector_child_nested {I : SelectorInterval} (h : I.left < I.right)
    (side : Bool) :
    I.left ≤ (selectorChild I side).left ∧ (selectorChild I side).right ≤ I.right := by
  cases side <;> simp only [selectorChild, Bool.false_eq_true, ↓reduceIte] <;>
    dsimp [selectorLength] <;> constructor <;> linarith

theorem selector_query_within {I : SelectorInterval} (h : I.left < I.right) (q : Fin 4) :
    selectorQueryPoint I q ∈ Set.Icc I.left I.right := by
  fin_cases q <;> simp [selectorQueryPoint, selectorLength, Set.mem_Icc] <;>
    (try constructor) <;> linarith

theorem selector_secant_symm (F : ℝ → ℝ) (a b : ℝ) :
    selectorSecant F a b = selectorSecant F b a := by
  simp only [selectorSecant]
  rw [show F a - F b = -(F b - F a) by ring,
    show a - b = -(b - a) by ring, neg_div_neg_eq]

theorem selector_secant_ordered {u v : ℝ} {F : ℝ → ℝ}
    (hF : ConvexOn ℝ (Set.Icc u v) F) {a b c d : ℝ}
    (ha : a ∈ Set.Icc u v) (hd : d ∈ Set.Icc u v)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    selectorSecant F a b ≤ selectorSecant F c d := by
  have hbd : b < d := hbc.trans_lt hcd
  have hb : b ∈ Set.Icc u v := ⟨ha.1.trans hab.le, hbd.le.trans hd.2⟩
  have hc : c ∈ Set.Icc u v := ⟨ha.1.trans (hab.le.trans hbc), hcd.le.trans hd.2⟩
  have h₁ : selectorSecant F a b ≤ selectorSecant F b d :=
    hF.slope_mono_adjacent ha hd hab hbd
  have h₂ : selectorSecant F d b ≤ selectorSecant F d c :=
    hF.secant_mono hd hb hc hbd.ne hcd.ne hbc
  rw [selector_secant_symm F d b, selector_secant_symm F d c] at h₂
  exact h₁.trans h₂

theorem selector_potential_nonnegative {u v : ℝ} {F : ℝ → ℝ}
    (hF : ConvexOn ℝ (Set.Icc u v) F) {I : SelectorInterval}
    (hI : I.left < I.right) (hl : u ≤ I.left) (hr : I.right ≤ v) :
    0 ≤ selectorPotential F I := by
  apply sub_nonneg.mpr
  apply selector_secant_ordered hF
    (show I.left ∈ Set.Icc u v from ⟨hl, hI.le.trans hr⟩)
    (show I.right ∈ Set.Icc u v from ⟨hl.trans hI.le, hr⟩)
  all_goals dsimp [selectorLength]; linarith

theorem selector_children_sum {u v : ℝ} {F : ℝ → ℝ}
    (hF : ConvexOn ℝ (Set.Icc u v) F) {I : SelectorInterval}
    (hI : I.left < I.right) (hl : u ≤ I.left) (hr : I.right ≤ v) :
    selectorPotential F (selectorChild I false) +
      selectorPotential F (selectorChild I true) ≤ selectorPotential F I := by
  have member {x : ℝ} (h₁ : I.left ≤ x) (h₂ : x ≤ I.right) : x ∈ Set.Icc u v :=
    ⟨hl.trans h₁, h₂.trans hr⟩
  have left_bound : selectorSecant F I.left (I.left + selectorLength I / 4) ≤
      selectorSecant F (selectorChild I false).left
        ((selectorChild I false).left + selectorLength (selectorChild I false) / 4) := by
    apply selector_secant_ordered hF
    · exact member le_rfl hI.le
    · apply member <;> simp [selectorChild, selectorLength] <;> linarith
    all_goals simp [selectorChild, selectorLength] <;> linarith
  have middle_bound :
      selectorSecant F ((selectorChild I false).right -
        selectorLength (selectorChild I false) / 4) (selectorChild I false).right ≤
      selectorSecant F (selectorChild I true).left
        ((selectorChild I true).left + selectorLength (selectorChild I true) / 4) := by
    apply selector_secant_ordered hF
    · apply member <;> simp [selectorChild, selectorLength] <;> linarith
    · apply member <;> simp [selectorChild, selectorLength] <;> linarith
    all_goals simp [selectorChild, selectorLength] <;> linarith
  have right_bound :
      selectorSecant F ((selectorChild I true).right -
        selectorLength (selectorChild I true) / 4) (selectorChild I true).right ≤
      selectorSecant F (I.right - selectorLength I / 4) I.right := by
    apply selector_secant_ordered hF
    · apply member <;> simp [selectorChild, selectorLength] <;> linarith
    · exact member hI.le le_rfl
    all_goals simp [selectorChild, selectorLength] <;> linarith
  dsimp [selectorPotential]
  linarith

theorem selector_potential_as_estimate {I : SelectorInterval} (hI : I.left < I.right)
    (F : ℝ → ℝ) :
    selectorPotential F I = selectorEstimate I (F ∘ selectorQueryPoint I) := by
  have hL := (selector_length_pos hI).ne'
  simp only [selectorPotential, selectorSecant, selectorEstimate, Function.comp_apply,
    selectorQueryPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have h₁ : I.right - (I.right - selectorLength I / 4) = selectorLength I / 4 := by ring
  have h₂ : I.left + selectorLength I / 4 - I.left = selectorLength I / 4 := by ring
  rw [h₁, h₂]
  field_simp
  ring

theorem selector_estimate_error {I : SelectorInterval} (hI : I.left < I.right)
    (F : ℝ → ℝ) (values : Fin 4 → ℝ)
    (herror : ∀ q, |values q - F (selectorQueryPoint I q)| ≤ selectorTolerance I) :
    |selectorEstimate I values - selectorPotential F I| ≤ 1 / 64 := by
  have hL := selector_length_pos hI
  have h₀ := abs_le.mp (herror 0)
  have h₁ := abs_le.mp (herror 1)
  have h₂ := abs_le.mp (herror 2)
  have h₃ := abs_le.mp (herror 3)
  rw [selector_potential_as_estimate hI F]
  dsimp only [selectorEstimate, Function.comp_apply]
  rw [← sub_div, abs_le, le_div_iff₀ hL, div_le_iff₀ hL]
  dsimp [selectorTolerance] at h₀ h₁ h₂ h₃
  constructor <;> linarith

theorem selector_defect_le {u v : ℝ} {F : ℝ → ℝ}
    (hF : ConvexOn ℝ (Set.Icc u v) F) {I : SelectorInterval}
    (hI : I.left < I.right) (hl : u ≤ I.left) (hr : I.right ≤ v) :
    F (selectorCenter I + selectorRadius I) + F (selectorCenter I - selectorRadius I) -
      2 * F (selectorCenter I) ≤ selectorRadius I * selectorPotential F I := by
  have member {x : ℝ} (h₁ : I.left ≤ x) (h₂ : x ≤ I.right) : x ∈ Set.Icc u v :=
    ⟨hl.trans h₁, h₂.trans hr⟩
  have left_bound : selectorSecant F I.left (I.left + selectorLength I / 4) ≤
      selectorSecant F (selectorCenter I - selectorRadius I) (selectorCenter I) := by
    apply selector_secant_ordered hF
    · exact member le_rfl hI.le
    · apply member <;> dsimp [selectorCenter] <;> linarith
    all_goals dsimp [selectorCenter, selectorRadius, selectorLength]; linarith
  have right_bound : selectorSecant F (selectorCenter I) (selectorCenter I + selectorRadius I) ≤
      selectorSecant F (I.right - selectorLength I / 4) I.right := by
    apply selector_secant_ordered hF
    · apply member <;> dsimp [selectorCenter] <;> linarith
    · exact member hI.le le_rfl
    all_goals dsimp [selectorCenter, selectorRadius, selectorLength]; linarith
  have hp : 0 < selectorRadius I := div_pos (selector_length_pos hI) (by norm_num)
  have hdiff : selectorSecant F (selectorCenter I) (selectorCenter I + selectorRadius I) -
      selectorSecant F (selectorCenter I - selectorRadius I) (selectorCenter I) ≤
      selectorPotential F I := by
    dsimp [selectorPotential]
    linarith
  have hid : F (selectorCenter I + selectorRadius I) +
      F (selectorCenter I - selectorRadius I) - 2 * F (selectorCenter I) =
      selectorRadius I *
        (selectorSecant F (selectorCenter I) (selectorCenter I + selectorRadius I) -
          selectorSecant F (selectorCenter I - selectorRadius I) (selectorCenter I)) := by
    simp only [selectorSecant, add_sub_cancel_left, sub_sub_cancel]
    field_simp
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hdiff hp.le

end KE02
