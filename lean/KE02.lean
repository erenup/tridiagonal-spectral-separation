import KE02.Statement
import KE02.EndpointProof
import KE02.Algorithm2Proof
import KE02.BasicSelectorProof
import KE02.GraeffeUniversal
import KE02.CoefficientProof
import KE02.RootExtractionProof
import KE02.ContinuantProof
import KE02.LocalConstantsProof
import KE02.WronskianProof

namespace KE02

/-- The aggregate certificate. -/
theorem coreCertificate : CoreCertificate :=
  ⟨endpointCertificate, algorithm2Certificate, basicSelectorCertificate, graeffeCertificate,
    coefficientCertificate, rootExtractionCertificate, continuantCertificate,
    localConstantsCertificate, wronskianCertificate⟩

end KE02
