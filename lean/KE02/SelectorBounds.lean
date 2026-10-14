import KE02.SelectorStatement
import Mathlib.Tactic

namespace KE02

theorem selector_threshold_reached (n : ℕ) : 16 * n ^ 3 ≤ 2 ^ selectorK n := by
  exact Nat.find_spec (show ∃ k : ℕ, selectorThreshold n ≤ 2 ^ k from
    ⟨selectorThreshold n, (selectorThreshold n).lt_two_pow_self.le⟩)

theorem selector_threshold_least (n j : ℕ) (hj : j < selectorK n) :
    2 ^ j < 16 * n ^ 3 := by
  exact Nat.lt_of_not_ge (Nat.find_min
    (show ∃ k : ℕ, selectorThreshold n ≤ 2 ^ k from
      ⟨selectorThreshold n, (selectorThreshold n).lt_two_pow_self.le⟩) hj)

theorem selector_threshold_upper (n : ℕ) (hn : 2 ≤ n) :
    2 ^ selectorK n < 32 * n ^ 3 := by
  have hnpos : 0 < n := by omega
  have hnpow : 0 < n ^ 3 := pow_pos hnpos _
  have hkpos : 0 < selectorK n := by
    have hr := selector_threshold_reached n
    by_contra hk
    have hk0 : selectorK n = 0 := by omega
    rw [hk0, pow_zero] at hr
    omega
  have hs : selectorK n - 1 + 1 = selectorK n := Nat.sub_add_cancel hkpos
  have hp := selector_threshold_least n (selectorK n - 1) (by omega)
  calc
    2 ^ selectorK n = 2 ^ (selectorK n - 1) * 2 := by
      nth_rw 1 [← hs]
      rw [pow_succ]
    _ < (16 * n ^ 3) * 2 := Nat.mul_lt_mul_of_pos_right hp (by decide)
    _ = 32 * n ^ 3 := by ring

theorem selector_radius_lower_bound (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ) :
    δ / (4096 * (n : ℝ) ^ 7) < δ / (4 * (n : ℝ) * 4 ^ selectorK n) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hupper : (2 : ℝ) ^ selectorK n < 32 * (n : ℝ) ^ 3 := by
    exact_mod_cast selector_threshold_upper n hn
  have hsq : ((2 : ℝ) ^ selectorK n) ^ 2 < (32 * (n : ℝ) ^ 3) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr hupper
  have hfour : (4 : ℝ) ^ selectorK n = ((2 : ℝ) ^ selectorK n) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hden : 4 * (n : ℝ) * 4 ^ selectorK n < 4096 * (n : ℝ) ^ 7 := by
    calc
      _ = (4 * (n : ℝ)) * ((2 : ℝ) ^ selectorK n) ^ 2 := by rw [hfour]
      _ < (4 * (n : ℝ)) * (32 * (n : ℝ) ^ 3) ^ 2 :=
        mul_lt_mul_of_pos_left hsq (by positivity)
      _ = _ := by ring
  exact div_lt_div_of_pos_left hδ (by positivity) hden

theorem selector_final_potential_bound (n : ℕ) (P0 Pk : ℝ)
    (hP0 : P0 < (n : ℝ) ^ 3)
    (hPk : Pk ≤ ((2 : ℝ) ^ selectorK n)⁻¹ * P0 +
      (1 / 16) * (1 - ((2 : ℝ) ^ selectorK n)⁻¹)) : Pk < 1 / 8 := by
  have hq : 0 < (2 : ℝ) ^ selectorK n := pow_pos (by norm_num) _
  have hi : 0 < ((2 : ℝ) ^ selectorK n)⁻¹ := inv_pos.mpr hq
  have hr : 16 * (n : ℝ) ^ 3 ≤ (2 : ℝ) ^ selectorK n := by
    exact_mod_cast selector_threshold_reached n
  have hf : ((2 : ℝ) ^ selectorK n)⁻¹ * (n : ℝ) ^ 3 ≤ 1 / 16 := by
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hq).mpr
    linarith
  have hp := mul_lt_mul_of_pos_left hP0 hi
  have he : (1 / 16 : ℝ) * (1 - ((2 : ℝ) ^ selectorK n)⁻¹) < 1 / 16 := by
    linarith
  linarith

end KE02
