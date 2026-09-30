import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Leaf001
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Leaf002

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (633/1024) (2895/4096) := by
  exact ⟨node001_checked, node002_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008
