import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached.Leaf002
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached.Leaf003
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached.Leaf004

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets (3675/4096) (127/128) node000 signNode000 := by
  exact ⟨⟨node002_checked, node003_checked⟩, node004_checked⟩

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime014.Cached.cover_checked
