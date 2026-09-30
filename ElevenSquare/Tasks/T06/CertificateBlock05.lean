import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger080
import ElevenSquare.Tasks.T06.CertificateInteger081
import ElevenSquare.Tasks.T06.CertificateInteger082
import ElevenSquare.Tasks.T06.CertificateInteger083
import ElevenSquare.Tasks.T06.CertificateInteger084
import ElevenSquare.Tasks.T06.CertificateInteger085
import ElevenSquare.Tasks.T06.CertificateInteger086
import ElevenSquare.Tasks.T06.CertificateInteger087
import ElevenSquare.Tasks.T06.CertificateInteger088
import ElevenSquare.Tasks.T06.CertificateInteger089
import ElevenSquare.Tasks.T06.CertificateInteger090
import ElevenSquare.Tasks.T06.CertificateInteger091
import ElevenSquare.Tasks.T06.CertificateInteger092
import ElevenSquare.Tasks.T06.CertificateInteger093
import ElevenSquare.Tasks.T06.CertificateInteger094
import ElevenSquare.Tasks.T06.CertificateInteger095

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock05 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 5 r) j s
      (dualNumerators (certificateBlockIndex 5 r) j s) ∧
    integerMassCheck (certificateBlockIndex 5 r) j s
      (dualNumerators (certificateBlockIndex 5 r) j s) := by
  fin_cases r
  · exact integerChecks080 j s
  · exact integerChecks081 j s
  · exact integerChecks082 j s
  · exact integerChecks083 j s
  · exact integerChecks084 j s
  · exact integerChecks085 j s
  · exact integerChecks086 j s
  · exact integerChecks087 j s
  · exact integerChecks088 j s
  · exact integerChecks089 j s
  · exact integerChecks090 j s
  · exact integerChecks091 j s
  · exact integerChecks092 j s
  · exact integerChecks093 j s
  · exact integerChecks094 j s
  · exact integerChecks095 j s

end ElevenSquare.Tasks.T06
