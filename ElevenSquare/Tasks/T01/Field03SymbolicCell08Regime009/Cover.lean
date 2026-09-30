import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (247/512) (2531/4096) := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009
