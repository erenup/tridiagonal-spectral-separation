import KE02.Statement
import KE02.SelectorProof
import KE02.GraeffeUniversal
import KE02.CoefficientProof

namespace KE02

/-- Complete scalar-selector contract and universal polynomial core. -/
theorem coreCertificate : CoreCertificate :=
  ⟨selectorCertificate, graeffeCertificate, coefficientCertificate⟩

end KE02
