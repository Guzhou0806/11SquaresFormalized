import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (633/1024) (1423/2048) := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010
