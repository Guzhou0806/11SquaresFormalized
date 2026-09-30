import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 8. -/
def sharedRosterCell08 : List QPoint := [((40697655775523476432821091/50000000000000000000000000), (120587362069840971382694247/50000000000000000000000000)), ((40947655775523476432821091/50000000000000000000000000), (120587362069840971382694247/50000000000000000000000000)), ((40447655775523476432821091/50000000000000000000000000), (120587362069840971382694247/50000000000000000000000000)), ((40697655775523476432821091/50000000000000000000000000), (120837362069840971382694247/50000000000000000000000000)), ((40697655775523476432821091/50000000000000000000000000), (120337362069840971382694247/50000000000000000000000000)), ((498139531/500000000), (2372449569/1000000000)), ((498139531/500000000), (2428498689/1000000000)), ((932288437/1000000000), (2458970549/1000000000)), ((883979663/1000000000), (2477149369/1000000000)), ((796533677/1000000000), (2424747549/1000000000)), ((202333959/250000000), (2390131547/1000000000)), ((829224961/1000000000), (293480237/125000000)), ((858241827/1000000000), (1161373501/500000000)), ((480957141/500000000), (2356980063/1000000000))]

theorem sharedRosterCell08_owned (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell08, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell08, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point009_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate010_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate011_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_012] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate012_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_013] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate013_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell08_owned
