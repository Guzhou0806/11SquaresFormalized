import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (203/1024) (679/2048) := by
  exact ⟨⟨node002_checked, node003_checked⟩, ⟨node005_checked, node006_checked⟩⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime004
