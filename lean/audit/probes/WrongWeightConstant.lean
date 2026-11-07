import KE02

open KE02

example (t h x : ℝ) (hh : 0 < h) :
    triangleWeight (t - h / 4) (h / 4) x + triangleWeight (t + h / 4) (h / 4) x ≤
      4 / 3 * triangleWeight t h x := coreCertificate.basicSelector.weights t h x hh

example (t h x : ℝ) (hh : 0 < h) :
    triangleWeight (t - h / 4) (h / 4) x + triangleWeight (t + h / 4) (h / 4) x ≤
      5 / 4 * triangleWeight t h x := coreCertificate.basicSelector.weights t h x hh
