import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (1/256) (1/128) := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
