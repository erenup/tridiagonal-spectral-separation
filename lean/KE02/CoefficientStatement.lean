import KE02.CoefficientDefinitions

namespace KE02

/-- Universal coefficient expansion, largest-product bounds and algebraic ratio bounds.
The coefficients are taken from an actual polynomial product. Positivity and ordering
are hypotheses only for the inequalities. The ratio-root analytic accuracy theorem,
spectral interpretation and arithmetic complexity are outside this statement. -/
structure CoefficientCertificate : Prop where
  expansion : ∀ (n : ℕ) (r : Fin n → ℝ) (k j : ℕ), j ≤ n →
    elementaryCoeff r k j =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        ∏ i ∈ s, r i ^ (2 ^ k)
  leading : ∀ (n : ℕ) (r : Fin n → ℝ) (k : ℕ), elementaryCoeff r k 0 = 1
  positive : ∀ (n : ℕ) (r : Fin n → ℝ) (k j : ℕ),
    (∀ i, 0 < r i) → j ≤ n → 0 < elementaryCoeff r k j
  bounds : ∀ (n : ℕ) (r : Fin n → ℝ) (k j : ℕ),
    (∀ i, 0 < r i) → Antitone r → j ≤ n →
    leadingRootProduct r k j ≤ elementaryCoeff r k j ∧
    elementaryCoeff r k j ≤ (n.choose j : ℝ) * leadingRootProduct r k j ∧
    (n.choose j : ℝ) * leadingRootProduct r k j ≤ (2 : ℝ) ^ n * leadingRootProduct r k j
  ratio_bounds : ∀ (n : ℕ) (r : Fin n → ℝ) (k : ℕ) (i : Fin n),
    (∀ a, 0 < r a) → Antitone r →
    r i ^ (2 ^ k) / (2 : ℝ) ^ n ≤
      elementaryCoeff r k (i.val + 1) / elementaryCoeff r k i.val ∧
    elementaryCoeff r k (i.val + 1) / elementaryCoeff r k i.val ≤
      (2 : ℝ) ^ n * r i ^ (2 ^ k)

end KE02
