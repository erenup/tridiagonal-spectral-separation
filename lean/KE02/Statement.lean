import KE02.EndpointStatement
import KE02.Algorithm2Statement
import KE02.BasicSelectorStatement
import KE02.GraeffeStatement
import KE02.CoefficientStatement
import KE02.RootExtractionStatement
import KE02.ContinuantStatement
import KE02.LocalConstantsStatement
import KE02.WronskianStatement

/-!
# The aggregate statement

Every component is a structure of universally quantified statements with
all hypotheses explicit. There is no spectral, matrix-gap, oracle-cost or
complexity assumption at this level.
-/

namespace KE02

/-- The finite and scalar core of the paper:
* `endpoint`: (13) and (33) nonnegative, inequality (34), Lemma 4.2;
* `algorithm2`: the threshold `K`, `θ`, the constants and the actual
  transcript of Algorithm 2 (Theorem 4.2 without Proposition 3.1);
* `basicSelector`: Lemma 4.1, one refinement of Algorithm 1, and the
  constants of Theorem 4.1 and Remark 4.1;
* `graeffe`, `coefficients`, `rootExtraction`, `continuant`: Appendix A;
* `localConstants`, `wronskian`: the scalar arithmetic of Section 3 and the
  discrete Wronskian identity (22). -/
structure CoreCertificate : Prop where
  endpoint : EndpointCertificate
  algorithm2 : Algorithm2Certificate
  basicSelector : BasicSelectorCertificate
  graeffe : GraeffeCertificate
  coefficients : CoefficientCertificate
  rootExtraction : RootExtractionCertificate
  continuant : ContinuantCertificate
  localConstants : LocalConstantsCertificate
  wronskian : WronskianCertificate

end KE02
