import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Cached.Leaf001
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Cached.Leaf002

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (633/1024) (2895/4096) node000 signNode000 := by
  exact ⟨node001_checked, node002_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.Cached.cover_checked
