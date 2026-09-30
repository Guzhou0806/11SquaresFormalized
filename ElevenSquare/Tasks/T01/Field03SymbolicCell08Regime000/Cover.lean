import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.Leaf001
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.Leaf002

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (1/4096) (5/128) := by
  exact ⟨node001_checked, node002_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000
