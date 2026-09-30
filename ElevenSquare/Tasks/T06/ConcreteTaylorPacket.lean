import ElevenSquare.Tasks.T06.ConcreteTaylorRows
import ElevenSquare.Tasks.T06.GradientsPacket

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxRecDepth 10000

theorem proposedPacket_rowsTaylorBound : RowsTaylorBound T constructionSquare proposedPacket := by
  apply rowsTaylorBound_of_curvatures T constructionSquare proposedPacket
    proposedPacket_rowsTied
  intro b i g hg
  exact concrete_row_curvature (branchRows b i) g hg

end
end ElevenSquare.Tasks.T06
