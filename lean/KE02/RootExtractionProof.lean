import KE02.RootExtractionStatement
import KE02.GraeffeUniversal
import KE02.CoefficientRatios
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

noncomputable section

namespace KE02

theorem graeffeCoeff_eq {n : ℕ} (r : Fin n → ℝ) (k j : ℕ) :
    graeffeCoeff r k j = elementaryCoeff r k j := by
  unfold graeffeCoeff elementaryCoeff poweredRootPolynomial
  rw [graeffeIterate_rootPolynomial]

theorem graeffeCoeff_bounds {n : ℕ} (r : Fin n → ℝ) (k j : ℕ) (hr : ∀ i, 0 < r i)
    (hmono : Antitone r) (hj : j ≤ n) :
    leadingRootProduct r k j ≤ graeffeCoeff r k j ∧
      graeffeCoeff r k j ≤ (2 : ℝ) ^ n * leadingRootProduct r k j := by
  rw [graeffeCoeff_eq]
  obtain ⟨h₁, h₂, h₃⟩ := elementaryCoeff_bounds r k j hr hmono hj
  exact ⟨h₁, h₂.trans h₃⟩

/-- `(x ^ (2^k)) ^ (1/2^k) = x` for `x ≥ 0`. -/
theorem pow_two_pow_rpow_inv {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ (2 ^ k)) ^ (1 / (2 ^ k : ℝ)) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  push_cast
  rw [mul_one_div_cancel (by positivity), Real.rpow_one]

theorem two_pow_rpow_inv (n k : ℕ) :
    ((2 : ℝ) ^ n) ^ (1 / (2 ^ k : ℝ)) = (2 : ℝ) ^ ((n : ℝ) / 2 ^ k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_one_div]

theorem ratio_root {n : ℕ} (r : Fin n → ℝ) (k : ℕ) (i : Fin n) (hr : ∀ a, 0 < r a)
    (hmono : Antitone r) :
    r i * (2 : ℝ) ^ (-(n : ℝ) / 2 ^ k) ≤ rootEstimate r k i ∧
      rootEstimate r k i ≤ r i * (2 : ℝ) ^ ((n : ℝ) / 2 ^ k) := by
  obtain ⟨hlo, hhi⟩ := elementaryCoeff_ratio_bounds r k i hr hmono
  unfold rootEstimate
  rw [graeffeCoeff_eq, graeffeCoeff_eq]
  have hri := (hr i).le
  have hz : (0 : ℝ) ≤ 1 / (2 ^ k : ℝ) := by positivity
  have hP : (0 : ℝ) ≤ r i ^ (2 ^ k) := by positivity
  have hratio : 0 ≤ elementaryCoeff r k (i.val + 1) / elementaryCoeff r k i.val :=
    div_nonneg (elementaryCoeff_pos r k _ hr i.isLt).le (elementaryCoeff_pos r k _ hr i.isLt.le).le
  constructor
  · have := Real.rpow_le_rpow (div_nonneg hP (by positivity)) hlo hz
    rw [Real.div_rpow hP (by positivity), pow_two_pow_rpow_inv hri, two_pow_rpow_inv] at this
    rw [neg_div, Real.rpow_neg (by norm_num), ← div_eq_mul_inv]
    exact this
  · have := Real.rpow_le_rpow hratio hhi hz
    rw [Real.mul_rpow (by positivity) hP, pow_two_pow_rpow_inv hri, two_pow_rpow_inv] at this
    rw [mul_comm]
    exact this

theorem iteratedSqrt_eq (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    iteratedSqrt k x = x ^ (1 / (2 ^ k : ℝ)) := by
  induction k with
  | zero => simp [iteratedSqrt]
  | succ k ih =>
    unfold iteratedSqrt at ih ⊢
    rw [Function.iterate_succ_apply', ih, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    congr 1
    rw [pow_succ]
    field_simp

theorem two_rpow_sub_one_le (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) : (2 : ℝ) ^ x - 1 ≤ x := by
  have h := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hx hx'
  norm_num at h
  linarith

theorem root_error {n : ℕ} (r : Fin n → ℝ) (k : ℕ) (i : Fin n) (hr : ∀ a, 0 < r a)
    (hmono : Antitone r) (h4 : r i < 4) (hnR : (n : ℝ) ≤ 2 ^ k) :
    |rootEstimate r k i - r i| ≤ 4 * n / 2 ^ k := by
  obtain ⟨hlo, hhi⟩ := ratio_root r k i hr hmono
  set x : ℝ := (n : ℝ) / 2 ^ k with hxdef
  have hR : (0 : ℝ) < 2 ^ k := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one hR]; exact hnR
  set y : ℝ := (2 : ℝ) ^ x with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow (by norm_num) hx0
  have hyx : y - 1 ≤ x := two_rpow_sub_one_le x hx0 hx1
  have hneg : (2 : ℝ) ^ (-(n : ℝ) / 2 ^ k) = y⁻¹ := by
    rw [neg_div, Real.rpow_neg (by norm_num)]
  rw [hneg] at hlo
  have hy0 : 0 < y := by linarith
  have hinv : 2 - y ≤ y⁻¹ := by
    rw [← one_div, le_div_iff₀ hy0]
    nlinarith [sq_nonneg (y - 1)]
  have hri := hr i
  have a₁ : r i * (y - 1) ≤ r i * x := mul_le_mul_of_nonneg_left hyx hri.le
  have a₂ : r i * x ≤ 4 * x := mul_le_mul_of_nonneg_right h4.le hx0
  have a₃ : r i * (2 - y) ≤ r i * y⁻¹ := mul_le_mul_of_nonneg_left hinv hri.le
  have e : 4 * (n : ℝ) / 2 ^ k = 4 * x := by rw [hxdef]; ring
  rw [e, abs_le]
  constructor <;> nlinarith

theorem graeffeSteps_spec (n : ℕ) (η : ℝ) (hn : 1 ≤ n) (hη : 0 < η) (hη1 : η < 1) :
    8 * (n : ℝ) / η ≤ 2 ^ graeffeSteps n η ∧ (2 : ℝ) ^ graeffeSteps n η < 16 * n / η ∧
      (n : ℝ) ≤ 2 ^ graeffeSteps n η ∧ 4 * (n : ℝ) / 2 ^ graeffeSteps n η ≤ η / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hspec : 8 * (n : ℝ) / η ≤ 2 ^ graeffeSteps n η := Nat.find_spec (exists_two_pow_ge _)
  have hx8 : (8 : ℝ) * n < 8 * n / η := by
    rw [lt_div_iff₀ hη]
    nlinarith
  have hk0 : graeffeSteps n η ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hspec
    linarith
  obtain ⟨m, hm⟩ : ∃ m, graeffeSteps n η = m + 1 := ⟨graeffeSteps n η - 1, by omega⟩
  have hmin : ¬ (8 * (n : ℝ) / η ≤ 2 ^ m) :=
    Nat.find_min (exists_two_pow_ge _) (show m < graeffeSteps n η by omega)
  have hlt : (2 : ℝ) ^ m < 8 * n / η := lt_of_not_ge hmin
  have hR : (0 : ℝ) < 8 * n / η := by positivity
  refine ⟨hspec, ?_, by linarith, ?_⟩
  · rw [hm, pow_succ]
    have : 16 * (n : ℝ) / η = 2 * (8 * n / η) := by ring
    linarith
  · calc 4 * (n : ℝ) / 2 ^ graeffeSteps n η ≤ 4 * n / (8 * n / η) :=
          div_le_div_of_nonneg_left (by positivity) hR hspec
      _ = η / 2 := by field_simp; ring

theorem graeffeSteps_least (n : ℕ) (η : ℝ) (hη : 0 < η) :
    8 * (n : ℝ) ≤ 2 ^ graeffeSteps n η * η ∧ ∀ k < graeffeSteps n η, (2 : ℝ) ^ k * η < 8 * n := by
  have hspec : 8 * (n : ℝ) / η ≤ 2 ^ graeffeSteps n η := Nat.find_spec (exists_two_pow_ge _)
  refine ⟨(div_le_iff₀ hη).mp hspec, fun k hk => ?_⟩
  have hmin : ¬ (8 * (n : ℝ) / η ≤ 2 ^ k) := Nat.find_min (exists_two_pow_ge _) hk
  exact (lt_div_iff₀ hη).mp (lt_of_not_ge hmin)

theorem graeffeDoubling_eq (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ fuel k, k ≤ graeffeSteps n η → graeffeSteps n η ≤ k + fuel →
      graeffeDoubling n η fuel k (2 ^ k) = graeffeSteps n η := by
  obtain ⟨hK, hmin⟩ := graeffeSteps_least n η hη
  intro fuel
  induction fuel with
  | zero =>
    intro k h₁ h₂
    simp only [graeffeDoubling]
    omega
  | succ fuel ih =>
    intro k h₁ h₂
    simp only [graeffeDoubling]
    split_ifs with h
    · by_contra hne
      exact absurd h (not_le.mpr (hmin k (lt_of_le_of_ne h₁ hne)))
    · have hlt : k < graeffeSteps n η :=
        lt_of_le_of_ne h₁ (fun e => h (by rw [e]; exact hK))
      rw [show 2 * (2 : ℝ) ^ k = 2 ^ (k + 1) by ring]
      exact ih (k + 1) hlt (by omega)

theorem graeffeDoubling_spec (n : ℕ) (η : ℝ) (fuel : ℕ) (hη : 0 < η)
    (hfuel : graeffeSteps n η ≤ fuel) : graeffeDoubling n η fuel 0 1 = graeffeSteps n η := by
  have h := graeffeDoubling_eq n η hη fuel 0 (Nat.zero_le _) (by omega)
  simpa using h

theorem sum_weights (n : ℕ) : ∑ j : Fin n, ((j : ℝ) + 1) = (n : ℝ) * (n + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℝ) + 1) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem weighted_abs_le {n : ℕ} (lam lamHat : Fin n → ℝ) (η : ℝ)
    (h : ∀ j, |lamHat j - lam j| ≤ η) :
    |∑ j : Fin n, ((j : ℝ) + 1) * lamHat j - ∑ j : Fin n, ((j : ℝ) + 1) * lam j| ≤
      (∑ j : Fin n, ((j : ℝ) + 1)) * η := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  calc |∑ j : Fin n, (((j : ℝ) + 1) * lamHat j - ((j : ℝ) + 1) * lam j)| ≤
        ∑ j : Fin n, |((j : ℝ) + 1) * lamHat j - ((j : ℝ) + 1) * lam j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, ((j : ℝ) + 1) * |lamHat j - lam j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    _ ≤ ∑ j : Fin n, ((j : ℝ) + 1) * η :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (by positivity)

theorem weighted_error {n : ℕ} (lam lamHat : Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ j, |lamHat j - lam j| ≤ ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) :
    |∑ j : Fin n, ((j : ℝ) + 1) * lamHat j - ∑ j : Fin n, ((j : ℝ) + 1) * lam j| ≤ ε := by
  have hb := weighted_abs_le lam lamHat _ h
  set W := ∑ i : Fin n, ((i : ℝ) + 1) with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => by positivity
  rcases eq_or_lt_of_le hW0 with h0 | hpos
  · rw [← h0] at hb
    have h0' : (0 : ℝ) * (ε / 0 / 2) ≤ ε := by simp [hε]
    exact hb.trans h0'
  · rw [show W * (ε / W / 2) = ε / 2 by field_simp] at hb
    linarith

theorem sum_error {n : ℕ} (lam lamHat : Fin n → ℝ) (η : ℝ)
    (h : ∀ j, |lamHat j - lam j| ≤ η) :
    |∑ j : Fin n, ((j : ℝ) + 1) * lamHat j - ∑ j : Fin n, ((j : ℝ) + 1) * lam j| ≤
      (n : ℝ) * (n + 1) / 2 * η := by
  rw [← sum_weights n]
  exact weighted_abs_le lam lamHat η h

theorem pipeline {n : ℕ} (r : Fin n → ℝ) (ε : ℝ) (hn : 1 ≤ n) (hr : ∀ a, 0 < r a ∧ r a < 4)
    (hmono : Antitone r) (hε : 0 < ε) (hε1 : ε < 1) :
    Monotone (fun j : Fin n => r j.rev - 2) ∧
    (∀ j : Fin n,
      |(iteratedSqrt (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1)))
          (graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) (j.rev.val + 1) /
            graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) j.rev.val) - 2) -
        (r j.rev - 2)| ≤ ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) ∧
    |∑ j : Fin n, ((j : ℝ) + 1) *
        (iteratedSqrt (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1)))
          (graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) (j.rev.val + 1) /
            graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) j.rev.val) - 2) -
      ∑ j : Fin n, ((j : ℝ) + 1) * (r j.rev - 2)| ≤
        (n : ℝ) * (n + 1) / 2 * (ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) ∧
    (n : ℝ) * (n + 1) / 2 * (ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) ≤ ε := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hW1 : 1 ≤ ∑ i : Fin n, ((i : ℝ) + 1) := by
    rw [sum_weights]
    nlinarith
  have hη0 : 0 < ε / ∑ i : Fin n, ((i : ℝ) + 1) := div_pos hε (by linarith)
  have hη1 : ε / ∑ i : Fin n, ((i : ℝ) + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨_, _, hnR, h4⟩ := graeffeSteps_spec n _ hn hη0 hη1
  have hpos : ∀ a, 0 < r a := fun a => (hr a).1
  have hj : ∀ j : Fin n,
      |(iteratedSqrt (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1)))
          (graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) (j.rev.val + 1) /
            graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) j.rev.val) - 2) -
        (r j.rev - 2)| ≤ ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2 := by
    intro j
    have hratio : 0 ≤
        graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) (j.rev.val + 1) /
          graeffeCoeff r (graeffeSteps n (ε / ∑ i : Fin n, ((i : ℝ) + 1))) j.rev.val := by
      rw [graeffeCoeff_eq, graeffeCoeff_eq]
      exact div_nonneg (elementaryCoeff_pos r _ _ hpos j.rev.isLt).le
        (elementaryCoeff_pos r _ _ hpos j.rev.isLt.le).le
    rw [iteratedSqrt_eq _ hratio, sub_sub_sub_cancel_right]
    have := root_error r _ j.rev hpos hmono (hr j.rev).2 hnR
    unfold rootEstimate at this
    linarith
  refine ⟨?_, hj, sum_error _ _ _ hj, ?_⟩
  · intro a b hab
    have := hmono (Fin.rev_le_rev.mpr hab)
    simp only
    linarith
  · rw [← sum_weights n, show (∑ i : Fin n, ((i : ℝ) + 1)) *
        (ε / (∑ i : Fin n, ((i : ℝ) + 1)) / 2) = ε / 2 by field_simp]
    linarith

theorem rootExtractionCertificate : RootExtractionCertificate where
  graeffe_coeff := fun _ r k j => graeffeCoeff_eq r k j
  coeff_bounds := fun _ r k j hr hm hj => graeffeCoeff_bounds r k j hr hm hj
  ratio_root := fun _ r k i hr hm => ratio_root r k i hr hm
  iterated_sqrt := fun k _ hx => iteratedSqrt_eq k hx
  two_rpow_sub_one_le := two_rpow_sub_one_le
  root_error := fun _ r k i hr hm h4 hnR => root_error r k i hr hm h4 hnR
  steps_least := graeffeSteps_least
  steps_doubling := fun n η fuel hη hfuel => graeffeDoubling_spec n η fuel hη hfuel
  steps_choice := graeffeSteps_spec
  weighted_error := fun _ lam lamHat ε hε h => weighted_error lam lamHat ε hε h
  sum_error := fun _ lam lamHat η h => sum_error lam lamHat η h
  pipeline := fun _ r ε hn hr hm hε hε1 => pipeline r ε hn hr hm hε hε1

end KE02
