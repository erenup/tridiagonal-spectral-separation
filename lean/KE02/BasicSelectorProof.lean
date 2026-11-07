import KE02.BasicSelectorStatement
import KE02.Algorithm2Proof
import Mathlib.Tactic

noncomputable section

namespace KE02

theorem weights_le (t h x : ℝ) (hh : 0 < h) :
    triangleWeight (t - h / 4) (h / 4) x + triangleWeight (t + h / 4) (h / 4) x ≤
      4 / 3 * triangleWeight t h x := by
  unfold triangleWeight
  set u := (x - t) / h with hu
  have hq : 0 < h / 4 := by positivity
  have e₁ : |x - (t - h / 4)| / (h / 4) = |4 * u + 1| := by
    rw [← abs_of_pos hq, ← abs_div, abs_of_pos hq, hu]
    congr 1
    field_simp
    ring
  have e₂ : |x - (t + h / 4)| / (h / 4) = |4 * u - 1| := by
    rw [← abs_of_pos hq, ← abs_div, abs_of_pos hq, hu]
    congr 1
    field_simp
    ring
  have e₃ : |x - t| / h = |u| := by
    rw [hu, abs_div, abs_of_pos hh]
  rw [e₁, e₂, e₃]
  rcases abs_cases (4 * u + 1) with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;>
    rcases abs_cases (4 * u - 1) with ⟨h₂, _⟩ | ⟨h₂, _⟩ <;>
    rcases abs_cases u with ⟨h₃, _⟩ | ⟨h₃, _⟩ <;>
    rw [h₁, h₂, h₃] <;> simp only [max_def] <;> split_ifs <;> linarith

theorem weights_attained (t h : ℝ) (hh : 0 < h) :
    triangleWeight (t - h / 4) (h / 4) (t - h / 4) +
        triangleWeight (t + h / 4) (h / 4) (t - h / 4) =
      4 / 3 * triangleWeight t h (t - h / 4) := by
  unfold triangleWeight
  have e₁ : t - h / 4 - (t + h / 4) = -(h / 2) := by ring
  have e₂ : t - h / 4 - t = -(h / 4) := by ring
  rw [sub_self, e₁, e₂, abs_zero, abs_neg, abs_neg, abs_of_pos (by positivity : 0 < h / 2),
    abs_of_pos (by positivity : 0 < h / 4)]
  have a : 1 - h / 2 / (h / 4) = -1 := by field_simp; norm_num
  have b : 1 - h / 4 / h = 3 / 4 := by field_simp; norm_num
  rw [a, b, zero_div, sub_zero]
  norm_num

/-- The summed form behind (29), from three three-point convexity inequalities. -/
theorem basic_children_sum {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) (h t : ℝ) (hh : 0 < h) :
    centeredVariation F (h / 4) (t - h / 4) + centeredVariation F (h / 4) (t + h / 4) ≤
      4 / 3 * centeredVariation F h t := by
  have i₁ := hF.secant_mono_aux1 (Set.mem_univ (t - h)) (Set.mem_univ (t - h / 4))
    (show t - h < t - h / 2 by linarith) (show t - h / 2 < t - h / 4 by linarith)
  have i₂ := hF.secant_mono_aux1 (Set.mem_univ (t - h / 4)) (Set.mem_univ (t + h / 4))
    (show t - h / 4 < t by linarith) (show t < t + h / 4 by linarith)
  have i₃ := hF.secant_mono_aux1 (Set.mem_univ (t + h / 4)) (Set.mem_univ (t + h))
    (show t + h / 4 < t + h / 2 by linarith) (show t + h / 2 < t + h by linarith)
  have j₁ : 3 * F (t - h / 2) ≤ F (t - h) + 2 * F (t - h / 4) := by nlinarith
  have j₂ : 2 * F t ≤ F (t - h / 4) + F (t + h / 4) := by nlinarith
  have j₃ : 3 * F (t + h / 2) ≤ 2 * F (t + h / 4) + F (t + h) := by nlinarith
  unfold centeredVariation
  rw [show t - h / 4 + h / 4 = t by ring, show t - h / 4 - h / 4 = t - h / 2 by ring,
    show t + h / 4 + h / 4 = t + h / 2 by ring, show t + h / 4 - h / 4 = t by ring]
  have key : 4 * (F t - F (t - h / 4)) - 4 * (F (t - h / 4) - F (t - h / 2)) +
      (4 * (F (t + h / 2) - F (t + h / 4)) - 4 * (F (t + h / 4) - F t)) ≤
        4 / 3 * ((F (t + h) - F t) - (F t - F (t - h))) := by linarith
  have e : (F t - F (t - h / 4)) / (h / 4) - (F (t - h / 4) - F (t - h / 2)) / (h / 4) +
      ((F (t + h / 2) - F (t + h / 4)) / (h / 4) - (F (t + h / 4) - F t) / (h / 4)) =
      (4 * (F t - F (t - h / 4)) - 4 * (F (t - h / 4) - F (t - h / 2)) +
        (4 * (F (t + h / 2) - F (t + h / 4)) - 4 * (F (t + h / 4) - F t))) / h := by
    field_simp
  have e' : 4 / 3 * ((F (t + h) - F t) / h - (F t - F (t - h)) / h) =
      4 / 3 * ((F (t + h) - F t) - (F t - F (t - h))) / h := by
    field_simp
  rw [e, e']
  exact div_le_div_of_nonneg_right key hh.le

theorem basic_contraction {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) (h t : ℝ) (hh : 0 < h) :
    min (centeredVariation F (h / 4) (t - h / 4)) (centeredVariation F (h / 4) (t + h / 4)) ≤
      2 / 3 * centeredVariation F h t := by
  have hs := basic_children_sum hF h t hh
  rcases le_total (centeredVariation F (h / 4) (t - h / 4))
      (centeredVariation F (h / 4) (t + h / 4)) with hle | hle
  · rw [min_eq_left hle]; linarith
  · rw [min_eq_right hle]; linarith

theorem basic_estimate_error (F : ℝ → ℝ) {r : ℝ} (c lower middle upper : ℝ) (hr : 0 < r)
    (e₀ : |lower - F (c - r)| ≤ r / 256) (e₁ : |middle - F c| ≤ r / 256)
    (e₂ : |upper - F (c + r)| ≤ r / 256) :
    |centeredEstimate r lower middle upper - centeredVariation F r c| ≤ 1 / 64 := by
  have := centered_estimate_error_tol F c lower middle upper hr e₀ e₁ e₂
  rw [show 4 * (r / 256) / r = 1 / 64 by field_simp; norm_num] at this
  exact this

theorem basic_step {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) (h t : ℝ) (v : Fin 5 → ℝ)
    (hh : 0 < h) (hv : ∀ i : Fin 5, |v i - F (basicPoint (h / 4) t i)| ≤ h / 4 / 256) :
    centeredVariation F (h / 4)
        (selectCenter (h / 4) t (centeredEstimate (h / 4) (v 0) (v 1) (v 2))
          (centeredEstimate (h / 4) (v 2) (v 3) (v 4))) ≤
      2 / 3 * centeredVariation F h t + 1 / 32 := by
  have hq : 0 < h / 4 := by positivity
  have hs := basic_children_sum hF h t hh
  have v₂ := hv 2
  simp only [basicPoint] at v₂
  have eL := basic_estimate_error F (t - h / 4) (v 0) (v 1) (v 2) hq
    (by simpa [basicPoint] using hv 0) (by simpa [basicPoint] using hv 1)
    (by simpa [sub_add_cancel] using v₂)
  have eR := basic_estimate_error F (t + h / 4) (v 2) (v 3) (v 4) hq
    (by simpa [add_sub_cancel_right] using v₂) (by simpa [basicPoint] using hv 3)
    (by simpa [basicPoint] using hv 4)
  have aL := abs_le.mp eL
  have aR := abs_le.mp eR
  unfold selectCenter
  split_ifs with hlr
  · linarith
  · linarith

theorem basic_initial (n : ℕ) (F : ℝ → ℝ) (h t : ℝ) (hn : 1 ≤ n) (hh : 0 < h)
    (hslope : ∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) :
    centeredVariation F h t < (n : ℝ) ^ 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [centeredVariation_eq_secant]
  have h₁ := (hslope t (t + h) (by linarith)).2
  have h₂ := (hslope (t - h) t (by linarith)).1
  nlinarith

theorem basicK_spec (n : ℕ) : 16 * (n : ℝ) ^ 3 ≤ (3 / 2 : ℝ) ^ basicK n ∧
    ∀ k < basicK n, (3 / 2 : ℝ) ^ k < 16 * (n : ℝ) ^ 3 :=
  ⟨Nat.find_spec (exists_three_halves_pow_ge _),
    fun _ hk => lt_of_not_ge (Nat.find_min (exists_three_halves_pow_ge _) hk)⟩

theorem basicK_ceil (n : ℕ) (hn : 1 ≤ n) :
    basicK n = ⌈Real.logb (3 / 2) (16 * (n : ℝ) ^ 3)⌉₊ := by
  have hx : (0 : ℝ) < 16 * (n : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have key : ∀ k : ℕ, ⌈Real.logb (3 / 2) (16 * (n : ℝ) ^ 3)⌉₊ ≤ k ↔
      16 * (n : ℝ) ^ 3 ≤ (3 / 2 : ℝ) ^ k := by
    intro k
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow (by norm_num) hx, Real.rpow_natCast]
  apply le_antisymm
  · exact Nat.find_min' _ ((key _).mp le_rfl)
  · exact (key _).mpr (basicK_spec n).1

theorem basicK_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ basicK n := by
  by_contra h
  have h0 : basicK n = 0 := by omega
  have hs := (basicK_spec n).1
  rw [h0, pow_zero] at hs
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ this
  linarith

theorem first_term (n : ℕ) : (2 / 3 : ℝ) ^ basicK n * (n : ℝ) ^ 3 ≤ 1 / 16 := by
  have hs := (basicK_spec n).1
  have hp : (0 : ℝ) < (3 / 2) ^ basicK n := by positivity
  rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, inv_pow, inv_mul_eq_div,
    div_le_div_iff₀ hp (by norm_num)]
  linarith

theorem basic_iterate (n : ℕ) (s : ℕ → ℝ) (h0 : s 0 < (n : ℝ) ^ 3)
    (hs : ∀ j, s (j + 1) ≤ 2 / 3 * s j + 1 / 32) :
    ∀ j, s j < (2 / 3 : ℝ) ^ j * (n : ℝ) ^ 3 + 1 / 32 * ∑ l ∈ Finset.range j, (2 / 3 : ℝ) ^ l := by
  intro j
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have e : ∑ l ∈ Finset.range (j + 1), (2 / 3 : ℝ) ^ l =
        2 / 3 * ∑ l ∈ Finset.range j, (2 / 3 : ℝ) ^ l + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [pow_succ]
      ring
    rw [e, pow_succ]
    have := hs j
    nlinarith

theorem geometric (j : ℕ) : 1 / 32 * ∑ l ∈ Finset.range j, (2 / 3 : ℝ) ^ l < 3 / 32 := by
  rw [geom_sum_eq (by norm_num)]
  have : 0 < (2 / 3 : ℝ) ^ j := by positivity
  have e : ((2 / 3 : ℝ) ^ j - 1) / (2 / 3 - 1) = 3 - 3 * (2 / 3 : ℝ) ^ j := by
    field_simp
    ring
  rw [e]
  linarith

theorem basic_final (n : ℕ) (s : ℕ → ℝ) (h0 : s 0 < (n : ℝ) ^ 3)
    (hs : ∀ j, s (j + 1) ≤ 2 / 3 * s j + 1 / 32) : s (basicK n) < 5 / 32 := by
  have h₁ := basic_iterate n s h0 hs (basicK n)
  have h₂ := first_term n
  have h₃ := geometric (basicK n)
  linarith

/-- `4^(log_b x) = x^(log_b 4)` for `x > 0`. -/
theorem four_rpow_logb (b x : ℝ) (hx : 0 < x) :
    (4 : ℝ) ^ Real.logb b x = x ^ Real.logb b 4 := by
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hx]
  unfold Real.logb
  ring_nf

theorem basic_radius (n : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ) (j : ℕ) (hj : j ≤ basicK n) :
    δ / (8 * n) * (16 * (n : ℝ) ^ 3) ^ (-Real.logb (3 / 2) 4) < δ / (2 * n) / 4 ^ j := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := 16 * (n : ℝ) ^ 3 with hx
  have hx0 : 0 < x := by positivity
  have hK := basicK_pos n hn
  obtain ⟨m, hm⟩ : ∃ m, basicK n = m + 1 := ⟨basicK n - 1, by omega⟩
  have hmin : (3 / 2 : ℝ) ^ m < x := (basicK_spec n).2 m (by omega)
  have hlog : (m : ℝ) < Real.logb (3 / 2) x := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hx0, Real.rpow_natCast]
    exact hmin
  have hexp : ((basicK n : ℕ) : ℝ) < 1 + Real.logb (3 / 2) x := by
    rw [hm]
    push_cast
    linarith
  have h4K : (4 : ℝ) ^ basicK n < 4 * x ^ Real.logb (3 / 2) 4 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 4) hexp
    rw [Real.rpow_natCast, Real.rpow_add (by norm_num), Real.rpow_one, four_rpow_logb _ _ hx0]
      at this
    exact this
  have h4j : (4 : ℝ) ^ j ≤ 4 ^ basicK n := pow_le_pow_right₀ (by norm_num) hj
  have hxa : 0 < x ^ Real.logb (3 / 2) 4 := Real.rpow_pos_of_pos hx0 _
  have hd : 0 < δ / (2 * n) := by positivity
  rw [Real.rpow_neg hx0.le]
  calc δ / (8 * n) * (x ^ Real.logb (3 / 2) 4)⁻¹ = δ / (2 * n) / (4 * x ^ Real.logb (3 / 2) 4) := by
        field_simp
        ring
    _ < δ / (2 * n) / 4 ^ basicK n := div_lt_div_of_pos_left hd (by positivity) h4K
    _ ≤ δ / (2 * n) / 4 ^ j := div_le_div_of_nonneg_left hd.le (by positivity) h4j

theorem basic_radius_lt_one (n : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (j : ℕ) : δ / (2 * n) / 4 ^ j ≤ δ / (2 * n) ∧ δ / (2 * n) < 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  · rw [div_lt_one (by positivity)]
    nlinarith

theorem basicSelectorCertificate : BasicSelectorCertificate where
  weights := weights_le
  weights_attained := weights_attained
  children_sum := fun _ h t hF hh => basic_children_sum hF h t hh
  contraction := fun _ h t hF hh => basic_contraction hF h t hh
  estimate_error := fun F _ c lower middle upper hr e₀ e₁ e₂ =>
    basic_estimate_error F c lower middle upper hr e₀ e₁ e₂
  step := fun _ h t v hF hh hv => basic_step hF h t v hh hv
  initial := basic_initial
  Kb_spec := basicK_spec
  Kb_ceil := basicK_ceil
  first_term := first_term
  iterate := basic_iterate
  geometric := geometric
  final := basic_final
  stopping_constants := by norm_num
  calls := fun _ _ hj => by omega
  radius_lt_one := basic_radius_lt_one
  radius := basic_radius

end KE02
