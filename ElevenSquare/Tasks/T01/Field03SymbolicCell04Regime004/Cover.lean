import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime004.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime004.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime004.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime004.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime004
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked :
    node000.Check source targets (131/512) (1293/4096) := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime004
