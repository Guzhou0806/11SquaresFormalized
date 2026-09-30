import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime008.Data
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Blocker
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicPointTarget

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem block_target_facets :
    ∀ f ∈ symbolicPointTarget blockPoint (499999/1000000),
      f ∈ SymbolicCell01Regime008.target02 := by
  intro f hf
  norm_num [symbolicPointTarget, symbolicPointFacet,
    symbolicPointNormal, symbolicPointBound, blockPoint,
    List.finRange] at hf
  rcases hf with rfl | rfl | rfl | rfl
  all_goals norm_num [SymbolicCell01Regime008.target02]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.block_target_facets
