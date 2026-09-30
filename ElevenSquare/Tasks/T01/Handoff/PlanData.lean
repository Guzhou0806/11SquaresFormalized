import ElevenSquare.Tasks.T01.Handoff.RootData
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- DATA PORTING HOLE. Export the full finite ancestry/branch program.
Every terminal, interval, predecessor, and closed branch must be present for
the 71 selected groups. ReducedCoverage.inventory_covered proves that these
groups still cover all 1,931 original baseline cases. -/
def planData (g : Group) (k : Fin 2184) : Plan := by
  sorry

end
end ElevenSquare.Tasks.T01.Handoff
