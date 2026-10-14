import KE02.CoefficientExpansion
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds

namespace KE02

private theorem firstIndices_eq_map {n j : ℕ} (hj : j ≤ n) :
    (Finset.univ : Finset (Fin n)).filter (fun i => i.val < j) =
      (Finset.univ : Finset (Fin j)).map (Fin.castLEEmb hj) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro hi
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hi
    rw [← ha]
    exact a.isLt

private theorem firstIndices_card {n j : ℕ} (hj : j ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < j)).card = j := by
  rw [firstIndices_eq_map hj]
  simp

theorem leadingRootProduct_eq_prod {n : ℕ} (r : Fin n → ℝ) (k j : ℕ) (hj : j ≤ n) :
    leadingRootProduct r k j = ∏ i : Fin j, r (Fin.castLE hj i) ^ (2 ^ k) := by
  unfold leadingRootProduct
  rw [firstIndices_eq_map hj, Finset.prod_map]
  rfl

theorem leadingRootProduct_pos {n : ℕ} (r : Fin n → ℝ) (k j : ℕ)
    (hr : ∀ i, 0 < r i) : 0 < leadingRootProduct r k j := by
  exact Finset.prod_pos fun i _ => pow_pos (hr i) _

/-- In an increasing enumeration of a subset, the `i`th index is at least `i`. -/
private theorem orderEmb_val_ge {n j : ℕ} (f : Fin j ↪o Fin n) (i : Fin j) :
    i.val ≤ (f i).val := by
  have h : ∀ (a : ℕ) (ha : a < j), a ≤ (f ⟨a, ha⟩).val := by
    intro a
    induction a with
    | zero => intro _; exact Nat.zero_le _
    | succ a ih =>
      intro ha
      have ha' : a < j := by omega
      have hi := ih ha'
      have hm := f.strictMono (show (⟨a, ha'⟩ : Fin j) < ⟨a + 1, ha⟩ from by
        exact Nat.lt_succ_self a)
      change (f ⟨a, ha'⟩).val < (f ⟨a + 1, ha⟩).val at hm
      omega
  exact h i.val i.isLt

/-- Every fixed-cardinality subset product is bounded by the corresponding prefix product. -/
theorem subset_prod_le_leadingRootProduct {n : ℕ} (r : Fin n → ℝ) (k j : ℕ)
    (hr : ∀ i, 0 < r i) (hmono : Antitone r) (hj : j ≤ n)
    (s : Finset (Fin n)) (hs : s.card = j) :
    (∏ i ∈ s, r i ^ (2 ^ k)) ≤ leadingRootProduct r k j := by
  have heq : (∏ i ∈ s, r i ^ (2 ^ k)) =
      ∏ i : Fin j, r (s.orderEmbOfFin hs i) ^ (2 ^ k) := by
    calc
      _ = ∏ i ∈ (Finset.univ : Finset (Fin j)).map (s.orderEmbOfFin hs).toEmbedding,
          r i ^ (2 ^ k) := by rw [s.map_orderEmbOfFin_univ hs]
      _ = _ := Finset.prod_map _ _ _
  rw [heq, leadingRootProduct_eq_prod r k j hj]
  apply Finset.prod_le_prod
  · intro i _
    exact (pow_pos (hr _) _).le
  · intro i _
    apply pow_le_pow_left₀ (hr _).le
    apply hmono
    exact orderEmb_val_ge (s.orderEmbOfFin hs) i

theorem elementaryCoeff_bounds {n : ℕ} (r : Fin n → ℝ) (k j : ℕ)
    (hr : ∀ i, 0 < r i) (hmono : Antitone r) (hj : j ≤ n) :
    leadingRootProduct r k j ≤ elementaryCoeff r k j ∧
    elementaryCoeff r k j ≤ (n.choose j : ℝ) * leadingRootProduct r k j ∧
    (n.choose j : ℝ) * leadingRootProduct r k j ≤ (2 : ℝ) ^ n * leadingRootProduct r k j := by
  have hprefix : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < j)) ∈
      (Finset.univ : Finset (Fin n)).powersetCard j := by
    exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, firstIndices_card hj⟩
  constructor
  · rw [elementaryCoeff_expansion r k j hj]
    exact Finset.single_le_sum (f := fun s : Finset (Fin n) => ∏ i ∈ s, r i ^ (2 ^ k))
      (fun s _ => (Finset.prod_pos fun i _ => pow_pos (hr i) _).le) hprefix
  constructor
  · rw [elementaryCoeff_expansion r k j hj]
    calc
      _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard j).card •
          leadingRootProduct r k j := by
        apply Finset.sum_le_card_nsmul
        intro s hs
        exact subset_prod_le_leadingRootProduct r k j hr hmono hj s
          (Finset.mem_powersetCard.mp hs).2
      _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]
  · apply mul_le_mul_of_nonneg_right _ (leadingRootProduct_pos r k j hr).le
    exact_mod_cast Nat.choose_le_two_pow n j

end KE02
