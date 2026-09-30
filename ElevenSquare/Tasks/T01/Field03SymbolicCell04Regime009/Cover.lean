import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime009.Leaf001
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime009.Leaf002

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime009
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (1433/2048) (743/1024) := by
  exact ⟨node001_checked, node002_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime009
