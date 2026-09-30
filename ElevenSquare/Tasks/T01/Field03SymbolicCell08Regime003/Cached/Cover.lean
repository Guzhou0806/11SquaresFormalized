import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Cached.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Cached.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Cached.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Cached.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (619/4096) (837/4096) node000 signNode000 := by
  exact ⟨⟨node002_checked, node003_checked⟩, ⟨node005_checked, node006_checked⟩⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime003.Cached.cover_checked
