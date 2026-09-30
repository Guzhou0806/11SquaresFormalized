import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (2847/4096) (751/1024) := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime011
