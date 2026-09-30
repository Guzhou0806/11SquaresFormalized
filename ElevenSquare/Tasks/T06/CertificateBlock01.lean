import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger016
import ElevenSquare.Tasks.T06.CertificateInteger017
import ElevenSquare.Tasks.T06.CertificateInteger018
import ElevenSquare.Tasks.T06.CertificateInteger019
import ElevenSquare.Tasks.T06.CertificateInteger020
import ElevenSquare.Tasks.T06.CertificateInteger021
import ElevenSquare.Tasks.T06.CertificateInteger022
import ElevenSquare.Tasks.T06.CertificateInteger023
import ElevenSquare.Tasks.T06.CertificateInteger024
import ElevenSquare.Tasks.T06.CertificateInteger025
import ElevenSquare.Tasks.T06.CertificateInteger026
import ElevenSquare.Tasks.T06.CertificateInteger027
import ElevenSquare.Tasks.T06.CertificateInteger028
import ElevenSquare.Tasks.T06.CertificateInteger029
import ElevenSquare.Tasks.T06.CertificateInteger030
import ElevenSquare.Tasks.T06.CertificateInteger031

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock01 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 1 r) j s
      (dualNumerators (certificateBlockIndex 1 r) j s) ∧
    integerMassCheck (certificateBlockIndex 1 r) j s
      (dualNumerators (certificateBlockIndex 1 r) j s) := by
  fin_cases r
  · exact integerChecks016 j s
  · exact integerChecks017 j s
  · exact integerChecks018 j s
  · exact integerChecks019 j s
  · exact integerChecks020 j s
  · exact integerChecks021 j s
  · exact integerChecks022 j s
  · exact integerChecks023 j s
  · exact integerChecks024 j s
  · exact integerChecks025 j s
  · exact integerChecks026 j s
  · exact integerChecks027 j s
  · exact integerChecks028 j s
  · exact integerChecks029 j s
  · exact integerChecks030 j s
  · exact integerChecks031 j s

end ElevenSquare.Tasks.T06
