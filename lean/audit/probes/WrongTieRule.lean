import KE02

open KE02

example (h t e : ℝ) : selectCenter h t e e = t - h := coreCertificate.endpoint.ties_left h t e

example (h t e : ℝ) : selectCenter h t e e = t + h := coreCertificate.endpoint.ties_left h t e
