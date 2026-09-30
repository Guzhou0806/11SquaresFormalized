import ElevenSquare.Tasks.T06.Branches
import ElevenSquare.Tasks.T06.DataPacket
import ElevenSquare.Tasks.T06.ConcreteTaylorUnavailable

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section

/-- All local feature choices are represented, with their original nonlinear
aliases, in one of the concrete packet's 128 branches. -/
theorem proposedPacket_branchCover : BranchCover T constructionSquare proposedPacket := by
  exact branch_cover_of_unavailable T constructionSquare proposedPacket
    (fun _ _ => rfl) concrete_unavailable_negative

end
end ElevenSquare.Tasks.T06
