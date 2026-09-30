import ElevenSquare.Tasks.T01.Handoff.Plan
import ElevenSquare.Tasks.T01.Handoff.Inventory
import ElevenSquare.Tasks.T01.ChartSubdivision
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- Closed uniform chart bins: the generic certificates use 32 bins, and the
field certificates may use the finer 256-bin partition. -/
def rootBinCount (g : Group) : ℕ := if g.val < 59 then 256 else 32

theorem rootBinCount_pos (g : Group) : 0 < rootBinCount g := by
  by_cases h : g.val < 59 <;> simp [rootBinCount, h]

/-- A concrete rational seed state for the occupied cells. Every bin covers its
closed angle interval; its owned points are strict interior points. Further
wall and ancestor refinements belong in the checked plan program. -/
def rootData (g : Group) (k : Fin 2184) : PoseState :=
  ElevenSquare.Tasks.T01.uniformSeedRoot (rootBinCount g) (caseMask k)

end
end ElevenSquare.Tasks.T01.Handoff
