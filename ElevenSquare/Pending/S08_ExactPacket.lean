import ElevenSquare.ConstructionData
import ElevenSquare.Pending.S08_Isolation
import ElevenSquare.Pending.S08_FeatureBranches
import ElevenSquare.Tasks.T06.PacketCompletion

/-! Concrete local isolation packet for the exact construction.
The task-private modules supply the geometric and finite certificate proofs. -/

namespace ElevenSquare.Pending
noncomputable section

-- This is the actual-data specialization.
-- Existence includes every algebraic derivative, feature choice, Taylor bound,
-- and all 128*33*2=8448 rational dual checks. No Python receipt is a premise.
theorem exact_local_packet_exists :
    ∃ p : LocalPacket, p.radii = focusedRadii ∧
      BranchCover T constructionSquare p ∧ RowsTied T constructionSquare p ∧
      RowsTaylorBound T constructionSquare p ∧ DualBounds T constructionSquare p := by
  exact ⟨ElevenSquare.Tasks.T06.proposedPacket, rfl,
    ElevenSquare.Tasks.T06.proposedPacket_branchCover,
    ElevenSquare.Tasks.T06.proposedPacket_rowsTied,
    ElevenSquare.Tasks.T06.proposedPacket_rowsTaylorBound,
    ElevenSquare.Tasks.T06.proposedPacket_dualBounds⟩

theorem construction_locally_isolated (h : Displacement)
    (hrect : InRectangle focusedRadii h)
    (hpack : LocalFeasible T constructionSquare h) : h = 0 := by
  obtain ⟨p, hp, hbranches, htied, htaylor, hdual⟩ := exact_local_packet_exists
  apply packet_isolates T constructionSquare p hbranches htied htaylor hdual h _ hpack
  rwa [hp]


end
end ElevenSquare.Pending
