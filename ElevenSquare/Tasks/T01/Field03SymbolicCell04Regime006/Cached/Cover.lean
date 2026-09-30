import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (1795/4096) (1119/2048) node000 signNode000 := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime006.Cached.cover_checked
