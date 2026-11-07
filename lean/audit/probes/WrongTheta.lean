import KE02

open KE02

example (F : ℝ → ℝ) (h t : ℝ) (hF : ConvexOn ℝ Set.univ F) (hh : 0 < h) :
    centeredVariation F h t ≤ endpointVariation F (1 / 2) h t :=
  coreCertificate.endpoint.centered_le_endpoint F (1 / 2) h t hF (by norm_num) le_rfl hh

example (F : ℝ → ℝ) (h t : ℝ) (hF : ConvexOn ℝ Set.univ F) (hh : 0 < h) :
    centeredVariation F h t ≤ endpointVariation F 1 h t :=
  coreCertificate.endpoint.centered_le_endpoint F 1 h t hF one_pos (by norm_num) hh
