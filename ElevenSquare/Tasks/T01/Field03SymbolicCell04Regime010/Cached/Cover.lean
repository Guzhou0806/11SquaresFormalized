import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached.Leaf001
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached.Leaf002

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (2973/4096) (1697/2048) node000 signNode000 := by
  exact ⟨node001_checked, node002_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached.cover_checked
