import KE02

open KE02

example : (1 : ℝ) / 8 + 1 / 128 + 1 / 64 < 1 / 2 := coreCertificate.algorithm2.stopping_constants

example : (1 : ℝ) / 8 + 1 / 128 + 1 / 64 < 1 / 8 := coreCertificate.algorithm2.stopping_constants
