import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (647/2048) (897/2048) := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime005
