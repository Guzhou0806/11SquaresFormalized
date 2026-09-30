import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (717/2048) (897/2048) := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007
