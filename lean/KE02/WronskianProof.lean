import KE02.WronskianStatement
import Mathlib.Tactic

namespace KE02

theorem wronskian_identity (n : ℕ) (d β a b : ℕ → ℝ) (lam mu : ℝ) (hβ : β 0 = 0)
    (ha : ∀ i, 1 ≤ i → i ≤ n → β (i - 1) * a (i - 1) + d i * a i + β i * a (i + 1) = lam * a i)
    (hb : ∀ i, 1 ≤ i → i ≤ n → β (i - 1) * b (i - 1) + d i * b i + β i * b (i + 1) = mu * b i) :
    ∀ i ≤ n, β i * (a i * b (i + 1) - a (i + 1) * b i) =
      (mu - lam) * ∑ j ∈ Finset.Icc 1 i, a j * b j := by
  intro i
  induction i with
  | zero => intro _; simp [hβ]
  | succ i ih =>
    intro hi
    have e₁ := ha (i + 1) (by omega) hi
    have e₂ := hb (i + 1) (by omega) hi
    simp only [Nat.add_sub_cancel] at e₁ e₂
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1)]
    have ih' := ih (by omega)
    linear_combination (-(b (i + 1))) * e₁ + a (i + 1) * e₂ + ih'

theorem abs_mul_le_half_sq (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]
  have := two_mul_le_add_sq |x| |y|
  rw [sq_abs, sq_abs] at this
  linarith

theorem partial_inner (n : ℕ) (a b : ℕ → ℝ) (ha : ∑ j ∈ Finset.Icc 1 n, a j ^ 2 = 1)
    (hb : ∑ j ∈ Finset.Icc 1 n, b j ^ 2 = 1) (hab : ∑ j ∈ Finset.Icc 1 n, a j * b j = 0) :
    ∀ i ≤ n, |∑ j ∈ Finset.Icc 1 i, a j * b j| ≤ 1 / 2 := by
  intro i hi
  have split : ∀ f : ℕ → ℝ, ∑ j ∈ Finset.Icc 1 n, f j =
      ∑ j ∈ Finset.Icc 1 i, f j + ∑ j ∈ Finset.Ico (i + 1) (n + 1), f j := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_consecutive _ (by omega) (by omega)]
  have hS := split (fun j => a j * b j)
  have hT : |∑ j ∈ Finset.Icc 1 n, a j * b j| ≤ ∑ j ∈ Finset.Icc 1 n, |a j * b j| :=
    Finset.abs_sum_le_sum_abs _ _
  set S := ∑ j ∈ Finset.Icc 1 i, a j * b j
  set T := ∑ j ∈ Finset.Ico (i + 1) (n + 1), a j * b j
  have hST : S + T = 0 := by rw [← hS]; exact hab
  have habs := split (fun j => |a j * b j|)
  have hS' : |S| ≤ ∑ j ∈ Finset.Icc 1 i, |a j * b j| := Finset.abs_sum_le_sum_abs _ _
  have hT' : |T| ≤ ∑ j ∈ Finset.Ico (i + 1) (n + 1), |a j * b j| := Finset.abs_sum_le_sum_abs _ _
  have hsum : ∑ j ∈ Finset.Icc 1 n, |a j * b j| ≤ 1 := by
    calc ∑ j ∈ Finset.Icc 1 n, |a j * b j| ≤ ∑ j ∈ Finset.Icc 1 n, (a j ^ 2 + b j ^ 2) / 2 :=
          Finset.sum_le_sum fun j _ => abs_mul_le_half_sq (a j) (b j)
      _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, ha, hb]; norm_num
  have hTS : |T| = |S| := by rw [show T = -S by linarith, abs_neg]
  have : |S| + |T| ≤ 1 := by
    linarith
  linarith

theorem wronskian_bound (n : ℕ) (d β a b : ℕ → ℝ) (lam mu γ : ℝ) (hβ : β 0 = 0)
    (ha : ∀ i, 1 ≤ i → i ≤ n → β (i - 1) * a (i - 1) + d i * a i + β i * a (i + 1) = lam * a i)
    (hb : ∀ i, 1 ≤ i → i ≤ n → β (i - 1) * b (i - 1) + d i * b i + β i * b (i + 1) = mu * b i)
    (na : ∑ j ∈ Finset.Icc 1 n, a j ^ 2 = 1) (nb : ∑ j ∈ Finset.Icc 1 n, b j ^ 2 = 1)
    (hab : ∑ j ∈ Finset.Icc 1 n, a j * b j = 0) (hγ : |lam - mu| ≤ γ) :
    ∀ i ≤ n, |β i| * |a i * b (i + 1) - a (i + 1) * b i| ≤ γ / 2 := by
  intro i hi
  rw [← abs_mul, wronskian_identity n d β a b lam mu hβ ha hb i hi, abs_mul]
  have h₁ := partial_inner n a b na nb hab i hi
  have h₂ : |mu - lam| ≤ γ := by rw [abs_sub_comm]; exact hγ
  have h₃ : 0 ≤ |∑ j ∈ Finset.Icc 1 i, a j * b j| := abs_nonneg _
  have h₄ : 0 ≤ |mu - lam| := abs_nonneg _
  nlinarith

theorem wronskianCertificate : WronskianCertificate where
  identity := wronskian_identity
  partial_inner := partial_inner
  bound := wronskian_bound

end KE02
