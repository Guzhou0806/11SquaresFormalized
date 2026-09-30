import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (3005/4096) (3355/4096) := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012
