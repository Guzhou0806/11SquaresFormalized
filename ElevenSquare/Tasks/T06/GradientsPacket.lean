import ElevenSquare.Tasks.T06.GradientsTies
import ElevenSquare.Tasks.T06.DataPacket

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem proposedPacket_rowsTied : RowsTied T constructionSquare proposedPacket := by
  intro b i
  refine ⟨proposedPacket_representative_mem b i, ?_⟩
  intro g hg
  exact ⟨(row_aliases_tied (branchRows b i) g hg).1,
    row_alias_gradient_eq (branchRows b i) g hg⟩

end
end ElevenSquare.Tasks.T06
