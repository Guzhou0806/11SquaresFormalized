import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger048
import ElevenSquare.Tasks.T06.CertificateInteger049
import ElevenSquare.Tasks.T06.CertificateInteger050
import ElevenSquare.Tasks.T06.CertificateInteger051
import ElevenSquare.Tasks.T06.CertificateInteger052
import ElevenSquare.Tasks.T06.CertificateInteger053
import ElevenSquare.Tasks.T06.CertificateInteger054
import ElevenSquare.Tasks.T06.CertificateInteger055
import ElevenSquare.Tasks.T06.CertificateInteger056
import ElevenSquare.Tasks.T06.CertificateInteger057
import ElevenSquare.Tasks.T06.CertificateInteger058
import ElevenSquare.Tasks.T06.CertificateInteger059
import ElevenSquare.Tasks.T06.CertificateInteger060
import ElevenSquare.Tasks.T06.CertificateInteger061
import ElevenSquare.Tasks.T06.CertificateInteger062
import ElevenSquare.Tasks.T06.CertificateInteger063

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock03 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 3 r) j s
      (dualNumerators (certificateBlockIndex 3 r) j s) ∧
    integerMassCheck (certificateBlockIndex 3 r) j s
      (dualNumerators (certificateBlockIndex 3 r) j s) := by
  fin_cases r
  · exact integerChecks048 j s
  · exact integerChecks049 j s
  · exact integerChecks050 j s
  · exact integerChecks051 j s
  · exact integerChecks052 j s
  · exact integerChecks053 j s
  · exact integerChecks054 j s
  · exact integerChecks055 j s
  · exact integerChecks056 j s
  · exact integerChecks057 j s
  · exact integerChecks058 j s
  · exact integerChecks059 j s
  · exact integerChecks060 j s
  · exact integerChecks061 j s
  · exact integerChecks062 j s
  · exact integerChecks063 j s

end ElevenSquare.Tasks.T06
