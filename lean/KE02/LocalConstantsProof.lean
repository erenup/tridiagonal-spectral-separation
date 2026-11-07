import KE02.LocalConstantsStatement
import Mathlib.Tactic

namespace KE02

theorem discarded_rows (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (1 / (2 * Real.sqrt n)) ^ 2 = 1 / 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  rw [div_pow, mul_pow, hs]
  field_simp
  ring

theorem direction_gap : (1 : ℝ) / 2 < Real.sqrt (3 / 8) := by
  rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `√γ ≤ 1/(16 n)` when `γ ≤ 1/(256 n²)`. -/
theorem sqrt_gamma_le (n : ℕ) (γ : ℝ) (hn : 1 ≤ n) (hγ' : γ ≤ 1 / (256 * (n : ℝ) ^ 2)) :
    Real.sqrt γ ≤ 1 / (16 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.sqrt γ ≤ Real.sqrt (1 / (256 * (n : ℝ) ^ 2)) := Real.sqrt_le_sqrt hγ'
    _ = 1 / (16 * n) := by
      rw [show 1 / (256 * (n : ℝ) ^ 2) = (1 / (16 * n)) ^ 2 by field_simp; ring,
        Real.sqrt_sq (by positivity)]

theorem tau_le (n : ℕ) (γ : ℝ) (hn : 1 ≤ n) (_hγ : 0 ≤ γ) (hγ' : γ ≤ 1 / (256 * (n : ℝ) ^ 2)) :
    4 * Real.sqrt (n * γ) ≤ 1 / (4 * Real.sqrt n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hg := sqrt_gamma_le n γ hn hγ'
  have hg0 : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  rw [Real.sqrt_mul hn'.le, le_div_iff₀ (by positivity)]
  have : 16 * (n : ℝ) * Real.sqrt γ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hg
    linarith
  nlinarith

theorem case_a (γ τ : ℝ) (hγ : 0 ≤ γ) (hτ : 0 < τ) : γ / (2 * τ ^ 2) ≤ 5 * γ / τ ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg τ, mul_nonneg hγ (sq_nonneg τ)]

theorem case_c (γ τ A B ρ : ℝ) (hγ : 0 ≤ γ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hA : τ < A)
    (hB : τ < B) (_hρ : 0 ≤ ρ) (hρτ : ρ ≤ τ) :
    2 * γ / (A * B) + γ * ρ / (2 * B) ≤ 5 * γ / τ ^ 2 := by
  have hA0 : 0 < A := hτ.trans hA
  have hB0 : 0 < B := hτ.trans hB
  have h₁ : 2 * γ / (A * B) ≤ 2 * γ / τ ^ 2 := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    rw [sq]
    exact mul_le_mul hA.le hB.le hτ.le hA0.le
  have h₂ : γ * ρ / (2 * B) ≤ γ / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ρ ≤ B := hρτ.trans hB.le
    nlinarith
  have h₃ : γ / 2 ≤ 3 * γ / τ ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : τ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have h₄ : 2 * γ / τ ^ 2 + 3 * γ / τ ^ 2 = 5 * γ / τ ^ 2 := by ring
  linarith

theorem total_change (n : ℕ) (γ : ℝ) (hn : 1 ≤ n) (hγ : 0 < γ) :
    5 * n * γ / (4 * Real.sqrt (n * γ)) ^ 2 = 5 / 16 ∧ (5 : ℝ) / 16 < 1 / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, by norm_num⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem truncation (n : ℕ) (γ : ℝ) (hn : 1 ≤ n) (hγ : 0 ≤ γ)
    (hγ' : γ ≤ 1 / (256 * (n : ℝ) ^ 2)) :
    2 * Real.sqrt n * (γ / 2 + Real.sqrt 2 * (4 * Real.sqrt (n * γ))) ≤
        4 * Real.sqrt n * (4 * Real.sqrt (n * γ)) ∧
      4 * Real.sqrt n * (4 * Real.sqrt (n * γ)) = 16 * n * Real.sqrt γ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn1
  have hg0 : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  have hgs : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ
  have hg := sqrt_gamma_le n γ hn hγ'
  have hg1 : Real.sqrt γ ≤ 1 := by
    refine hg.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [Real.sqrt_mul hn'.le]
  constructor
  · -- γ/2 ≤ (2 - √2) τ, using γ ≤ √γ and √n ≥ 1.
    have hγg : γ ≤ Real.sqrt γ := by nlinarith
    have hτ : Real.sqrt γ ≤ Real.sqrt n * Real.sqrt γ := by nlinarith
    have key : γ / 2 + Real.sqrt 2 * (4 * (Real.sqrt n * Real.sqrt γ)) ≤
        2 * (4 * (Real.sqrt n * Real.sqrt γ)) := by
      have : 0 ≤ (3 / 2 - Real.sqrt 2) * (Real.sqrt n * Real.sqrt γ) := by
        apply mul_nonneg (by linarith) (by positivity)
      nlinarith
    have hsn : 0 ≤ Real.sqrt n := by linarith
    nlinarith
  · nlinarith

theorem nuclear (n : ℕ) (γ a₁ a₂ : ℝ) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂)
    (b₁ : a₁ ≤ 16 * n * Real.sqrt γ) (b₂ : a₂ ≤ 16 * n * Real.sqrt γ) :
    3 * Real.sqrt 2 * Real.sqrt (a₁ ^ 2 + a₂ ^ 2) ≤ 96 * n * Real.sqrt γ := by
  set m := 16 * (n : ℝ) * Real.sqrt γ with hm
  have hm0 : 0 ≤ m := h₁.trans b₁
  have hsq : a₁ ^ 2 + a₂ ^ 2 ≤ 2 * m ^ 2 := by
    have := pow_le_pow_left₀ h₁ b₁ 2
    have := pow_le_pow_left₀ h₂ b₂ 2
    linarith
  have hroot : Real.sqrt (a₁ ^ 2 + a₂ ^ 2) ≤ Real.sqrt 2 * m := by
    calc Real.sqrt (a₁ ^ 2 + a₂ ^ 2) ≤ Real.sqrt (2 * m ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * m := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hm0]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  calc 3 * Real.sqrt 2 * Real.sqrt (a₁ ^ 2 + a₂ ^ 2) ≤ 3 * Real.sqrt 2 * (Real.sqrt 2 * m) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = 6 * m := by rw [show 3 * Real.sqrt 2 * (Real.sqrt 2 * m) =
          3 * (Real.sqrt 2 * Real.sqrt 2) * m by ring, h2]; ring
    _ = 96 * n * Real.sqrt γ := by rw [hm]; ring

theorem gamma_range (n : ℕ) (h : ℝ) (hn : 1 ≤ n) (hh : 0 < h) (hh1 : h ≤ 1) :
    0 < h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) ∧
      h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) ≤ 1 / (256 * (n : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hh2 : h ^ 2 ≤ 1 := by nlinarith
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have : 256 * (n : ℝ) ^ 2 ≤ 2 ^ 20 * (n : ℝ) ^ 4 := by nlinarith
  nlinarith

theorem aux_variation (G : ℝ → ℝ) (h t : ℝ) :
    (G (t + h) + G (t - h) - 2 * G t) / h = centeredVariation G h t := by
  unfold centeredVariation
  ring

theorem transfer (F G : ℝ → ℝ) (n N h t : ℝ) (hh : 0 < h)
    (e₀ : |F (t - h) - G (t - h)| ≤ n * N) (e₁ : |F t - G t| ≤ n * N)
    (e₂ : |F (t + h) - G (t + h)| ≤ n * N) :
    centeredVariation G h t - 4 * n / h * N ≤ centeredVariation F h t := by
  have key : centeredVariation G h t - centeredVariation F h t =
      ((G (t + h) - F (t + h)) - 2 * (G t - F t) + (G (t - h) - F (t - h))) / h := by
    unfold centeredVariation
    field_simp
    ring
  have a₀ := abs_le.mp e₀
  have a₁ := abs_le.mp e₁
  have a₂ := abs_le.mp e₂
  have hb : ((G (t + h) - F (t + h)) - 2 * (G t - F t) + (G (t - h) - F (t - h))) / h ≤
      4 * n / h * N := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hh]
    linarith
  linarith

theorem sqrt_gamma_eq (n : ℕ) (h : ℝ) (hn : 1 ≤ n) (hh : 0 < h) :
    Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)) = h / (2 ^ 10 * (n : ℝ) ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) = (h / (2 ^ 10 * (n : ℝ) ^ 2)) ^ 2 by
    field_simp, Real.sqrt_sq (by positivity)]

theorem prop31_constant (n : ℕ) (h : ℝ) (hn : 1 ≤ n) (hh : 0 < h) :
    1 - 384 * (n : ℝ) ^ 2 * Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)) / h = 5 / 8 ∧
      (384 : ℝ) / 1024 = 3 / 8 ∧ 1 - (3 : ℝ) / 8 = 5 / 8 ∧ (1 : ℝ) / 2 < 5 / 8 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, by norm_num, by norm_num, by norm_num⟩
  rw [sqrt_gamma_eq n h hn hh]
  field_simp
  ring

theorem prop31_chain (F G : ℝ → ℝ) (n : ℕ) (N h t : ℝ) (hn : 1 ≤ n) (hh : 0 < h)
    (hN : N ≤ 96 * n * Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)))
    (e₀ : |F (t - h) - G (t - h)| ≤ n * N) (e₁ : |F t - G t| ≤ n * N)
    (e₂ : |F (t + h) - G (t + h)| ≤ n * N) (hG : 1 ≤ centeredVariation G h t) :
    1 / 2 < centeredVariation F h t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := transfer F G n N h t hh e₀ e₁ e₂
  have hc := (prop31_constant n h hn hh).1
  have hcoef : 0 ≤ 4 * (n : ℝ) / h := by positivity
  have hmul : 4 * (n : ℝ) / h * N ≤
      4 * n / h * (96 * n * Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4))) :=
    mul_le_mul_of_nonneg_left hN hcoef
  have e : 4 * (n : ℝ) / h * (96 * n * Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4))) =
      384 * (n : ℝ) ^ 2 * Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)) / h := by
    field_simp
    ring
  linarith

theorem gap_chain (n : ℕ) (δ h : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hh : δ / (128 * (n : ℝ) ^ 4) < h) :
    (2 : ℝ)⁻¹ ^ 34 * δ ^ 2 / (n : ℝ) ^ 12 < h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < δ / (128 * (n : ℝ) ^ 4) := by positivity
  have hsq : (δ / (128 * (n : ℝ) ^ 4)) ^ 2 < h ^ 2 := pow_lt_pow_left₀ hh hpos.le (by norm_num)
  have e : (2 : ℝ)⁻¹ ^ 34 * δ ^ 2 / (n : ℝ) ^ 12 =
      (δ / (128 * (n : ℝ) ^ 4)) ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) := by
    field_simp
    ring
  rw [e]
  exact div_lt_div_of_pos_right hsq (by positivity)

theorem localConstantsCertificate : LocalConstantsCertificate where
  discarded_rows := discarded_rows
  direction_gap := direction_gap
  tau_le := tau_le
  case_a := case_a
  case_c := case_c
  total_change := total_change
  truncation := truncation
  nuclear := nuclear
  gamma_range := gamma_range
  aux_variation := aux_variation
  transfer := transfer
  constant := prop31_constant
  chain := prop31_chain
  gap_chain := gap_chain

end KE02
