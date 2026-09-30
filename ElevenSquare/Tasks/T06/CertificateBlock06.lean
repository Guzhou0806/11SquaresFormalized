import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger096
import ElevenSquare.Tasks.T06.CertificateInteger097
import ElevenSquare.Tasks.T06.CertificateInteger098
import ElevenSquare.Tasks.T06.CertificateInteger099
import ElevenSquare.Tasks.T06.CertificateInteger100
import ElevenSquare.Tasks.T06.CertificateInteger101
import ElevenSquare.Tasks.T06.CertificateInteger102
import ElevenSquare.Tasks.T06.CertificateInteger103
import ElevenSquare.Tasks.T06.CertificateInteger104
import ElevenSquare.Tasks.T06.CertificateInteger105
import ElevenSquare.Tasks.T06.CertificateInteger106
import ElevenSquare.Tasks.T06.CertificateInteger107
import ElevenSquare.Tasks.T06.CertificateInteger108
import ElevenSquare.Tasks.T06.CertificateInteger109
import ElevenSquare.Tasks.T06.CertificateInteger110
import ElevenSquare.Tasks.T06.CertificateInteger111

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock06 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 6 r) j s
      (dualNumerators (certificateBlockIndex 6 r) j s) ∧
    integerMassCheck (certificateBlockIndex 6 r) j s
      (dualNumerators (certificateBlockIndex 6 r) j s) := by
  fin_cases r
  · exact integerChecks096 j s
  · exact integerChecks097 j s
  · exact integerChecks098 j s
  · exact integerChecks099 j s
  · exact integerChecks100 j s
  · exact integerChecks101 j s
  · exact integerChecks102 j s
  · exact integerChecks103 j s
  · exact integerChecks104 j s
  · exact integerChecks105 j s
  · exact integerChecks106 j s
  · exact integerChecks107 j s
  · exact integerChecks108 j s
  · exact integerChecks109 j s
  · exact integerChecks110 j s
  · exact integerChecks111 j s

end ElevenSquare.Tasks.T06
