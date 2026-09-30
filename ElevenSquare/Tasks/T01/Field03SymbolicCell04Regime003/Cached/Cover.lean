import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (677/4096) (1195/4096) node000 signNode000 := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cached.cover_checked
