import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (3675/4096) (127/128) := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014
