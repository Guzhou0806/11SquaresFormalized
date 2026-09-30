import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger064
import ElevenSquare.Tasks.T06.CertificateInteger065
import ElevenSquare.Tasks.T06.CertificateInteger066
import ElevenSquare.Tasks.T06.CertificateInteger067
import ElevenSquare.Tasks.T06.CertificateInteger068
import ElevenSquare.Tasks.T06.CertificateInteger069
import ElevenSquare.Tasks.T06.CertificateInteger070
import ElevenSquare.Tasks.T06.CertificateInteger071
import ElevenSquare.Tasks.T06.CertificateInteger072
import ElevenSquare.Tasks.T06.CertificateInteger073
import ElevenSquare.Tasks.T06.CertificateInteger074
import ElevenSquare.Tasks.T06.CertificateInteger075
import ElevenSquare.Tasks.T06.CertificateInteger076
import ElevenSquare.Tasks.T06.CertificateInteger077
import ElevenSquare.Tasks.T06.CertificateInteger078
import ElevenSquare.Tasks.T06.CertificateInteger079

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock04 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 4 r) j s
      (dualNumerators (certificateBlockIndex 4 r) j s) ∧
    integerMassCheck (certificateBlockIndex 4 r) j s
      (dualNumerators (certificateBlockIndex 4 r) j s) := by
  fin_cases r
  · exact integerChecks064 j s
  · exact integerChecks065 j s
  · exact integerChecks066 j s
  · exact integerChecks067 j s
  · exact integerChecks068 j s
  · exact integerChecks069 j s
  · exact integerChecks070 j s
  · exact integerChecks071 j s
  · exact integerChecks072 j s
  · exact integerChecks073 j s
  · exact integerChecks074 j s
  · exact integerChecks075 j s
  · exact integerChecks076 j s
  · exact integerChecks077 j s
  · exact integerChecks078 j s
  · exact integerChecks079 j s

end ElevenSquare.Tasks.T06
