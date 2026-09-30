import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Leaf001
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Leaf002

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (2973/4096) (1697/2048) := by
  exact ⟨node001_checked, node002_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010
