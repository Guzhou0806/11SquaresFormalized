import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007.Leaf001
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007.Leaf002

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (65/128) (2531/4096) := by
  exact ⟨node001_checked, node002_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime007
