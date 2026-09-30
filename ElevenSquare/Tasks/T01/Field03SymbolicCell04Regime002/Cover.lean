import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (619/4096) (811/4096) := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime002
