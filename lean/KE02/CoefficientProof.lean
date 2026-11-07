import KE02.CoefficientRatios

namespace KE02

/-- All coefficient identities, positivity, ordered-product estimates and algebraic ratios. -/
theorem coefficientCertificate : CoefficientCertificate where
  expansion := fun _ r k j hj => elementaryCoeff_expansion r k j hj
  leading := fun _ r k => elementaryCoeff_zero r k
  positive := fun _ r k j hr hj => elementaryCoeff_pos r k j hr hj
  bounds := fun _ r k j hr hmono hj => elementaryCoeff_bounds r k j hr hmono hj
  ratio_bounds := fun _ r k i hr hmono => elementaryCoeff_ratio_bounds r k i hr hmono

end KE02
