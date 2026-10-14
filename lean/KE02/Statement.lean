import KE02.SelectorStatement
import KE02.GraeffeStatement
import KE02.CoefficientStatement

namespace KE02

/-- The robust scalar-selector contract and universal Graeffe/coefficient core.
Every hypothesis belongs to the explicit component statements. This structure
has no spectral, matrix-gap, eigenvalue-oracle or complexity assumption. -/
structure CoreCertificate : Prop where
  selector : SelectorCertificate
  graeffe : GraeffeCertificate
  coefficients : CoefficientCertificate

end KE02
