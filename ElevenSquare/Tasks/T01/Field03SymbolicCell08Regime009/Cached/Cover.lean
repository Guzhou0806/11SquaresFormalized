import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached.Leaf004
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached.Leaf005
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached.Leaf006

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (247/512) (2531/4096) node000 signNode000 := by
  exact ⟨⟨⟨node003_checked, node004_checked⟩, node005_checked⟩, node006_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime009.Cached.cover_checked
