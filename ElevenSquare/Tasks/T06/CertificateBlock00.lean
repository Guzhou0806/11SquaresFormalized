import ElevenSquare.Tasks.T06.CertificateBlockIndex
import ElevenSquare.Tasks.T06.CertificateInteger000
import ElevenSquare.Tasks.T06.CertificateInteger001
import ElevenSquare.Tasks.T06.CertificateInteger002
import ElevenSquare.Tasks.T06.CertificateInteger003
import ElevenSquare.Tasks.T06.CertificateInteger004
import ElevenSquare.Tasks.T06.CertificateInteger005
import ElevenSquare.Tasks.T06.CertificateInteger006
import ElevenSquare.Tasks.T06.CertificateInteger007
import ElevenSquare.Tasks.T06.CertificateInteger008
import ElevenSquare.Tasks.T06.CertificateInteger009
import ElevenSquare.Tasks.T06.CertificateInteger010
import ElevenSquare.Tasks.T06.CertificateInteger011
import ElevenSquare.Tasks.T06.CertificateInteger012
import ElevenSquare.Tasks.T06.CertificateInteger013
import ElevenSquare.Tasks.T06.CertificateInteger014
import ElevenSquare.Tasks.T06.CertificateInteger015

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certificateBlock00 (r : Fin 16) (j : Fin 33) (s : Fin 2) :
    integerResidualCheck (certificateBlockIndex 0 r) j s
      (dualNumerators (certificateBlockIndex 0 r) j s) ∧
    integerMassCheck (certificateBlockIndex 0 r) j s
      (dualNumerators (certificateBlockIndex 0 r) j s) := by
  fin_cases r
  · exact integerChecks000 j s
  · exact integerChecks001 j s
  · exact integerChecks002 j s
  · exact integerChecks003 j s
  · exact integerChecks004 j s
  · exact integerChecks005 j s
  · exact integerChecks006 j s
  · exact integerChecks007 j s
  · exact integerChecks008 j s
  · exact integerChecks009 j s
  · exact integerChecks010 j s
  · exact integerChecks011 j s
  · exact integerChecks012 j s
  · exact integerChecks013 j s
  · exact integerChecks014 j s
  · exact integerChecks015 j s

end ElevenSquare.Tasks.T06
