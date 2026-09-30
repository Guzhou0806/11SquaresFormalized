import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Cached.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Cached.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Cached.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Cached.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (717/2048) (897/2048) node000 signNode000 := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.Cached.cover_checked
