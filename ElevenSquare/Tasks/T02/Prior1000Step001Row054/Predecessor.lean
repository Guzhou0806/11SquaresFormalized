import ElevenSquare.Tasks.T02.Prior1000Step001Row054.TransitionData
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell009.PoseDomains
import ElevenSquare.Tasks.T02.RationalChecks

namespace ElevenSquare.Tasks.T02.Prior1000Step001Row054
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

theorem predecessor_matches_seed : predecessorRow = ElevenSquare.Tasks.T02.Prior1000Initialization.Cell009.poseCertificate.row 54 := by
  unfold predecessorRow CellRootCertificate.row uniformRow
  congr 1 <;> rational_decide

end
end ElevenSquare.Tasks.T02.Prior1000Step001Row054
