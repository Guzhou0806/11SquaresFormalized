import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (633/1024) (1423/2048) node000 signNode000 := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime010.Cached.cover_checked
