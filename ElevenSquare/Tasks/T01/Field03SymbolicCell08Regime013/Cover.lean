import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (3301/4096) (1837/2048) := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013
