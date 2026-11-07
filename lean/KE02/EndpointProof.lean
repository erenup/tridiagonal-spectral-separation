import KE02.EndpointStatement
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

namespace KE02

theorem secant_symm (F : ℝ → ℝ) (a b : ℝ) : secant F a b = secant F b a := by
  unfold secant
  rw [show F a - F b = -(F b - F a) by ring, show a - b = -(b - a) by ring, neg_div_neg_eq]

/-- For convex `F`, the secant slope over `[a, b]` is at most the secant
slope over `[c, d]` whenever `a ≤ c` and `b ≤ d`. -/
theorem secant_mono_of_le {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hac : a ≤ c) (hbd : b ≤ d) :
    secant F a b ≤ secant F c d := by
  have had : a < d := lt_of_lt_of_le hab hbd
  have h₁ : secant F a b ≤ secant F a d := by
    unfold secant
    exact hF.secant_mono (Set.mem_univ a) (Set.mem_univ b) (Set.mem_univ d) hab.ne'
      had.ne' hbd
  have h₂ : secant F d a ≤ secant F d c := by
    unfold secant
    exact hF.secant_mono (Set.mem_univ d) (Set.mem_univ a) (Set.mem_univ c) had.ne
      hcd.ne hac
  rw [secant_symm F d a, secant_symm F d c] at h₂
  exact h₁.trans h₂

theorem centeredVariation_eq_secant (F : ℝ → ℝ) (h t : ℝ) :
    centeredVariation F h t = secant F t (t + h) - secant F (t - h) t := by
  unfold centeredVariation secant
  rw [show t + h - t = h by ring, show t - (t - h) = h by ring]

theorem endpointVariation_eq_secant (F : ℝ → ℝ) (θ h t : ℝ) :
    endpointVariation F θ h t =
      secant F (t + (1 - 2 * θ) * h) (t + h) - secant F (t - h) (t - (1 - 2 * θ) * h) := by
  unfold endpointVariation secant
  rw [show t + h - (t + (1 - 2 * θ) * h) = 2 * θ * h by ring,
    show t - (1 - 2 * θ) * h - (t - h) = 2 * θ * h by ring]

theorem centeredVariation_eq_estimate (F : ℝ → ℝ) (h t : ℝ) :
    centeredVariation F h t = centeredEstimate h (F (t - h)) (F t) (F (t + h)) := rfl

theorem endpointVariation_eq_estimate (F : ℝ → ℝ) (θ h t : ℝ) :
    endpointVariation F θ h t =
      endpointEstimate θ h (F (t - h)) (F (t - (1 - 2 * θ) * h))
        (F (t + (1 - 2 * θ) * h)) (F (t + h)) := rfl

theorem centered_nonneg {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) {h : ℝ} (t : ℝ)
    (hh : 0 < h) : 0 ≤ centeredVariation F h t := by
  rw [centeredVariation_eq_secant]
  have := secant_mono_of_le hF (a := t - h) (b := t) (c := t) (d := t + h)
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

theorem endpoint_nonneg {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) {θ h : ℝ} (t : ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (hh : 0 < h) : 0 ≤ endpointVariation F θ h t := by
  rw [endpointVariation_eq_secant]
  have p := mul_pos hθ hh
  have := secant_mono_of_le hF (a := t - h) (b := t - (1 - 2 * θ) * h)
    (c := t + (1 - 2 * θ) * h) (d := t + h)
    (by linarith) (by linarith) (by nlinarith) (by nlinarith)
  linarith

/-- Inequality (34). -/
theorem centered_le_endpoint {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) {θ h : ℝ} (t : ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (hh : 0 < h) :
    centeredVariation F h t ≤ endpointVariation F θ h t := by
  rw [centeredVariation_eq_secant, endpointVariation_eq_secant]
  have p := mul_pos hθ hh
  have hl := secant_mono_of_le hF (a := t - h) (b := t - (1 - 2 * θ) * h) (c := t - h) (d := t)
    (by linarith) (by linarith) le_rfl (by nlinarith)
  have hr := secant_mono_of_le hF (a := t) (b := t + h) (c := t + (1 - 2 * θ) * h)
    (d := t + h) (by linarith) (by linarith) (by nlinarith) le_rfl
  linarith

theorem child_windows (θ h t : ℝ) :
    (t - (1 / 2 - θ) * h) - (1 / 2 - θ) * h = t - (1 - 2 * θ) * h ∧
    (t - (1 / 2 - θ) * h) + (1 / 2 - θ) * h = t ∧
    (t + (1 / 2 - θ) * h) - (1 / 2 - θ) * h = t ∧
    (t + (1 / 2 - θ) * h) + (1 / 2 - θ) * h = t + (1 - 2 * θ) * h := by
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem refinePoint_in_parent {θ h t : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 1 / 4) (hh : 0 < h)
    (i : Fin 7) :
    t - h ≤ refinePoint θ ((1 / 2 - θ) * h) t i ∧ refinePoint θ ((1 / 2 - θ) * h) t i ≤ t + h := by
  have p₁ := mul_pos hθ hh
  have p₂ : 0 ≤ θ * (θ * h) := (mul_pos hθ p₁).le
  have p₃ : 0 ≤ (1 / 2 - θ) * h := (mul_pos (by linarith) hh).le
  fin_cases i <;> refine ⟨?_, ?_⟩ <;> (try simp [refinePoint]) <;> nlinarith

theorem points_of_children (F : ℝ → ℝ) (θ h t : ℝ) :
    endpointVariation F θ h (t - h) =
      endpointEstimate θ h (F (refinePoint θ h t 0)) (F (refinePoint θ h t 1))
        (F (refinePoint θ h t 2)) (F (refinePoint θ h t 3)) ∧
    endpointVariation F θ h (t + h) =
      endpointEstimate θ h (F (refinePoint θ h t 3)) (F (refinePoint θ h t 4))
        (F (refinePoint θ h t 5)) (F (refinePoint θ h t 6)) := by
  constructor
  · rw [endpointVariation_eq_estimate]
    simp only [refinePoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_add_cancel]
  · rw [endpointVariation_eq_estimate]
    simp only [refinePoint, Matrix.cons_val, add_sub_cancel_right]

/-- The sum inequality in the proof of Lemma 4.2. -/
theorem endpoint_children_sum {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) {θ h : ℝ} (t : ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 4) (hh : 0 < h) :
    endpointVariation F θ ((1 / 2 - θ) * h) (t - (1 / 2 - θ) * h) +
      endpointVariation F θ ((1 / 2 - θ) * h) (t + (1 / 2 - θ) * h) ≤
        endpointVariation F θ h t := by
  simp only [endpointVariation_eq_secant]
  have p₁ := mul_pos hθ hh
  have p₂ : 0 < θ * ((1 / 2 - θ) * h) := mul_pos hθ (mul_pos (by linarith) hh)
  have p₃ : 0 ≤ θ * h * (1 - 2 * θ) := mul_nonneg p₁.le (by linarith)
  -- Parent left secant ≤ left child's left secant.
  have i₁ := secant_mono_of_le hF (a := t - h) (b := t - (1 - 2 * θ) * h)
    (c := t - (1 / 2 - θ) * h - (1 / 2 - θ) * h)
    (d := t - (1 / 2 - θ) * h - (1 - 2 * θ) * ((1 / 2 - θ) * h))
    (by linarith) (by linarith) (by linarith) (by linarith)
  -- Left child's right secant ≤ right child's left secant.
  have i₂ := secant_mono_of_le hF (a := t - (1 / 2 - θ) * h + (1 - 2 * θ) * ((1 / 2 - θ) * h))
    (b := t - (1 / 2 - θ) * h + (1 / 2 - θ) * h)
    (c := t + (1 / 2 - θ) * h - (1 / 2 - θ) * h)
    (d := t + (1 / 2 - θ) * h - (1 - 2 * θ) * ((1 / 2 - θ) * h))
    (by linarith) (by linarith) (by linarith) (by linarith)
  -- Right child's right secant ≤ parent right secant.
  have i₃ := secant_mono_of_le hF (a := t + (1 / 2 - θ) * h + (1 - 2 * θ) * ((1 / 2 - θ) * h))
    (b := t + (1 / 2 - θ) * h + (1 / 2 - θ) * h)
    (c := t + (1 - 2 * θ) * h) (d := t + h)
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- (35). -/
theorem endpoint_contraction {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) {θ h : ℝ} (t : ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 4) (hh : 0 < h) :
    min (endpointVariation F θ ((1 / 2 - θ) * h) (t - (1 / 2 - θ) * h))
        (endpointVariation F θ ((1 / 2 - θ) * h) (t + (1 / 2 - θ) * h)) ≤
      1 / 2 * endpointVariation F θ h t := by
  have hs := endpoint_children_sum hF t hθ hθ' hh
  rcases le_total (endpointVariation F θ ((1 / 2 - θ) * h) (t - (1 / 2 - θ) * h))
      (endpointVariation F θ ((1 / 2 - θ) * h) (t + (1 / 2 - θ) * h)) with hle | hle
  · rw [min_eq_left hle]; linarith
  · rw [min_eq_right hle]; linarith

theorem endpoint_estimate_error (F : ℝ → ℝ) {θ h : ℝ} (c v₀ v₁ v₂ v₃ : ℝ)
    (hθ : 0 < θ) (hh : 0 < h)
    (e₀ : |v₀ - F (c - h)| ≤ 2 * θ * h / 256)
    (e₁ : |v₁ - F (c - (1 - 2 * θ) * h)| ≤ 2 * θ * h / 256)
    (e₂ : |v₂ - F (c + (1 - 2 * θ) * h)| ≤ 2 * θ * h / 256)
    (e₃ : |v₃ - F (c + h)| ≤ 2 * θ * h / 256) :
    |endpointEstimate θ h v₀ v₁ v₂ v₃ - endpointVariation F θ h c| ≤ 1 / 64 := by
  have hd : 0 < 2 * θ * h := by positivity
  rw [endpointVariation_eq_estimate]
  unfold endpointEstimate
  have key : (v₃ - v₂) / (2 * θ * h) - (v₁ - v₀) / (2 * θ * h) -
      ((F (c + h) - F (c + (1 - 2 * θ) * h)) / (2 * θ * h) -
        (F (c - (1 - 2 * θ) * h) - F (c - h)) / (2 * θ * h)) =
      ((v₃ - F (c + h)) - (v₂ - F (c + (1 - 2 * θ) * h)) - (v₁ - F (c - (1 - 2 * θ) * h)) +
        (v₀ - F (c - h))) / (2 * θ * h) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have t₀ := abs_le.mp e₀
  have t₁ := abs_le.mp e₁
  have t₂ := abs_le.mp e₂
  have t₃ := abs_le.mp e₃
  rw [abs_le]
  constructor <;> linarith

theorem selectCenter_tie (h t e : ℝ) : selectCenter h t e e = t - h := by
  simp [selectCenter]

/-- (36) for one refinement with the actual replies. -/
theorem endpoint_potential_step {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) {θ h : ℝ} (t : ℝ)
    (v : Fin 7 → ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 4) (hh : 0 < h)
    (hv : ∀ i : Fin 7, |v i - F (refinePoint θ ((1 / 2 - θ) * h) t i)| ≤
      2 * θ * ((1 / 2 - θ) * h) / 256) :
    endpointVariation F θ ((1 / 2 - θ) * h)
        (selectCenter ((1 / 2 - θ) * h) t
          (endpointEstimate θ ((1 / 2 - θ) * h) (v 0) (v 1) (v 2) (v 3))
          (endpointEstimate θ ((1 / 2 - θ) * h) (v 3) (v 4) (v 5) (v 6))) ≤
      1 / 2 * endpointVariation F θ h t + 1 / 32 := by
  set h' := (1 / 2 - θ) * h with hh'
  have hpos : 0 < h' := mul_pos (by linarith) hh
  have hs := endpoint_children_sum hF t hθ hθ' hh
  rw [← hh'] at hs
  have eL := endpoint_estimate_error F (t - h') (v 0) (v 1) (v 2) (v 3) hθ hpos
    (by simpa [refinePoint] using hv 0) (by simpa [refinePoint] using hv 1)
    (by simpa [refinePoint] using hv 2) (by simpa [refinePoint] using hv 3)
  have eR := endpoint_estimate_error F (t + h') (v 3) (v 4) (v 5) (v 6) hθ hpos
    (by simpa [refinePoint] using hv 3) (by simpa [refinePoint] using hv 4)
    (by simpa [refinePoint] using hv 5) (by simpa [refinePoint] using hv 6)
  have aL := abs_le.mp eL
  have aR := abs_le.mp eR
  unfold selectCenter
  split_ifs with hlr
  · linarith
  · linarith

theorem endpointCertificate : EndpointCertificate where
  centered_nonneg := fun _ _ t hF hh => centered_nonneg hF t hh
  endpoint_nonneg := fun _ _ _ t hF hθ hθ' hh => endpoint_nonneg hF t hθ hθ' hh
  centered_le_endpoint := fun _ _ _ t hF hθ hθ' hh => centered_le_endpoint hF t hθ hθ' hh
  child_windows := child_windows
  points_in_parent := fun _ _ _ hθ hθ' hh i => refinePoint_in_parent hθ hθ' hh i
  points_of_children := points_of_children
  children_sum := fun _ _ _ t hF hθ hθ' hh => endpoint_children_sum hF t hθ hθ' hh
  contraction := fun _ _ _ t hF hθ hθ' hh => endpoint_contraction hF t hθ hθ' hh
  estimate_error := fun F _ _ c v₀ v₁ v₂ v₃ hθ hh e₀ e₁ e₂ e₃ =>
    endpoint_estimate_error F c v₀ v₁ v₂ v₃ hθ hh e₀ e₁ e₂ e₃
  ties_left := selectCenter_tie
  potential_step := fun _ _ _ t v hF hθ hθ' hh hv => endpoint_potential_step hF t v hθ hθ' hh hv

end KE02
