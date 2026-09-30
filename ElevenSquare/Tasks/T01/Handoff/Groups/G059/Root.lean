import ElevenSquare.Tasks.T01.Handoff.Plan
import ElevenSquare.Tasks.T01.Handoff.Inventory
import ElevenSquare.Tasks.T01.ChartSubdivision

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G059
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- The sole case in generic group 59. -/
def caseIndex : Fin 2184 := ⟨1705, by decide⟩

/-- An unconditional, conservative state for the recorded mask. Its 32 closed
angular bins match the historical trace's partition, while the center domains
are still the whole closed cells and ownership uses checked seed squares. -/
def root : PoseState := uniformSeedRoot 32 (caseMask caseIndex)

theorem root_rows_length (i : Owner) : (root.rows i).length = 32 := by
  simp [root, uniformSeedRoot, uniformRows]

theorem root_initialized : RootValid (caseMask caseIndex) root := by
  intro P hc hocc
  exact uniform_seed_root_initialized P 32 (by decide) (caseMask caseIndex) hc hocc

theorem case_mem_group : caseIndex.val ∈ groupCases ⟨59, by decide⟩ := by
  decide

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G059

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.root_initialized
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.case_mem_group
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G059.root_rows_length
