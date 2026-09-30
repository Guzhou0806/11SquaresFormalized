import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (619/4096) (837/4096) := by
  exact ⟨⟨node002_checked, node003_checked⟩, ⟨node005_checked, node006_checked⟩⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003
