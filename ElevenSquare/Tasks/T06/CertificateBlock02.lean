import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger032
import ElevenSquare.Tasks.T06.CertificateInteger033
import ElevenSquare.Tasks.T06.CertificateInteger034
import ElevenSquare.Tasks.T06.CertificateInteger035
import ElevenSquare.Tasks.T06.CertificateInteger036
import ElevenSquare.Tasks.T06.CertificateInteger037
import ElevenSquare.Tasks.T06.CertificateInteger038
import ElevenSquare.Tasks.T06.CertificateInteger039
import ElevenSquare.Tasks.T06.CertificateInteger040
import ElevenSquare.Tasks.T06.CertificateInteger041
import ElevenSquare.Tasks.T06.CertificateInteger042
import ElevenSquare.Tasks.T06.CertificateInteger043
import ElevenSquare.Tasks.T06.CertificateInteger044
import ElevenSquare.Tasks.T06.CertificateInteger045
import ElevenSquare.Tasks.T06.CertificateInteger046
import ElevenSquare.Tasks.T06.CertificateInteger047

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock02 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 2 r) j s
      (dualNumerators (certificateBlockIndex 2 r) j s) ∧
    integerMassCheck (certificateBlockIndex 2 r) j s
      (dualNumerators (certificateBlockIndex 2 r) j s) := by
  fin_cases r
  · exact integerChecks032 j s
  · exact integerChecks033 j s
  · exact integerChecks034 j s
  · exact integerChecks035 j s
  · exact integerChecks036 j s
  · exact integerChecks037 j s
  · exact integerChecks038 j s
  · exact integerChecks039 j s
  · exact integerChecks040 j s
  · exact integerChecks041 j s
  · exact integerChecks042 j s
  · exact integerChecks043 j s
  · exact integerChecks044 j s
  · exact integerChecks045 j s
  · exact integerChecks046 j s
  · exact integerChecks047 j s

end ElevenSquare.Tasks.T06
