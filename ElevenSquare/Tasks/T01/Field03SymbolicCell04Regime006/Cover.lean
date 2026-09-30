import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (1795/4096) (1119/2048) := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006
