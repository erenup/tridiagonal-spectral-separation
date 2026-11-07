import KE02.CoefficientBounds

namespace KE02

theorem leadingRootProduct_succ {n : ℕ} (r : Fin n → ℝ) (k : ℕ) (i : Fin n) :
    leadingRootProduct r k (i.val + 1) = leadingRootProduct r k i.val * r i ^ (2 ^ k) := by
  have hs : (Finset.univ : Finset (Fin n)).filter (fun a => a.val < i.val + 1) =
      insert i ((Finset.univ : Finset (Fin n)).filter (fun a => a.val < i.val)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hi : i ∉ (Finset.univ : Finset (Fin n)).filter (fun a => a.val < i.val) := by
    simp
  unfold leadingRootProduct
  rw [hs, Finset.prod_insert hi]
  exact mul_comm _ _

theorem elementaryCoeff_ratio_bounds {n : ℕ} (r : Fin n → ℝ) (k : ℕ) (i : Fin n)
    (hr : ∀ a, 0 < r a) (hmono : Antitone r) :
    r i ^ (2 ^ k) / (2 : ℝ) ^ n ≤
      elementaryCoeff r k (i.val + 1) / elementaryCoeff r k i.val ∧
    elementaryCoeff r k (i.val + 1) / elementaryCoeff r k i.val ≤
      (2 : ℝ) ^ n * r i ^ (2 ^ k) := by
  have hi : i.val ≤ n := Nat.le_of_lt i.isLt
  have hi' : i.val + 1 ≤ n := i.isLt
  obtain ⟨hlo, hhi, hchoose⟩ := elementaryCoeff_bounds r k i.val hr hmono hi
  obtain ⟨hlo', hhi', hchoose'⟩ := elementaryCoeff_bounds r k (i.val + 1) hr hmono hi'
  have he := elementaryCoeff_pos r k i.val hr hi
  have he' := elementaryCoeff_pos r k (i.val + 1) hr hi'
  have hp := leadingRootProduct_pos r k i.val hr
  have hp' := leadingRootProduct_pos r k (i.val + 1) hr
  have hc : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  constructor
  · calc
      r i ^ (2 ^ k) / (2 : ℝ) ^ n =
          leadingRootProduct r k (i.val + 1) /
            ((2 : ℝ) ^ n * leadingRootProduct r k i.val) := by
        rw [leadingRootProduct_succ]
        field_simp
      _ ≤ elementaryCoeff r k (i.val + 1) / elementaryCoeff r k i.val :=
        div_le_div₀ he'.le hlo' he (hhi.trans hchoose)
  · calc
      elementaryCoeff r k (i.val + 1) / elementaryCoeff r k i.val ≤
          ((2 : ℝ) ^ n * leadingRootProduct r k (i.val + 1)) /
            leadingRootProduct r k i.val :=
        div_le_div₀ (mul_pos hc hp').le (hhi'.trans hchoose') hp hlo
      _ = (2 : ℝ) ^ n * r i ^ (2 ^ k) := by
        rw [leadingRootProduct_succ]
        field_simp

end KE02
