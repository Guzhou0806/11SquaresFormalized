import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger112
import ElevenSquare.Tasks.T06.CertificateInteger113
import ElevenSquare.Tasks.T06.CertificateInteger114
import ElevenSquare.Tasks.T06.CertificateInteger115
import ElevenSquare.Tasks.T06.CertificateInteger116
import ElevenSquare.Tasks.T06.CertificateInteger117
import ElevenSquare.Tasks.T06.CertificateInteger118
import ElevenSquare.Tasks.T06.CertificateInteger119
import ElevenSquare.Tasks.T06.CertificateInteger120
import ElevenSquare.Tasks.T06.CertificateInteger121
import ElevenSquare.Tasks.T06.CertificateInteger122
import ElevenSquare.Tasks.T06.CertificateInteger123
import ElevenSquare.Tasks.T06.CertificateInteger124
import ElevenSquare.Tasks.T06.CertificateInteger125
import ElevenSquare.Tasks.T06.CertificateInteger126
import ElevenSquare.Tasks.T06.CertificateInteger127

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock07 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 7 r) j s
      (dualNumerators (certificateBlockIndex 7 r) j s) ∧
    integerMassCheck (certificateBlockIndex 7 r) j s
      (dualNumerators (certificateBlockIndex 7 r) j s) := by
  fin_cases r
  · exact integerChecks112 j s
  · exact integerChecks113 j s
  · exact integerChecks114 j s
  · exact integerChecks115 j s
  · exact integerChecks116 j s
  · exact integerChecks117 j s
  · exact integerChecks118 j s
  · exact integerChecks119 j s
  · exact integerChecks120 j s
  · exact integerChecks121 j s
  · exact integerChecks122 j s
  · exact integerChecks123 j s
  · exact integerChecks124 j s
  · exact integerChecks125 j s
  · exact integerChecks126 j s
  · exact integerChecks127 j s

end ElevenSquare.Tasks.T06
