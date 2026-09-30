import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 4. -/
def sharedRosterCell04 : List QPoint := [((159319997167449384989195311/200000000000000000000000000), (165192385068974431749720049/100000000000000000000000000)), ((160319997167449384989195311/200000000000000000000000000), (165192385068974431749720049/100000000000000000000000000)), ((158319997167449384989195311/200000000000000000000000000), (165192385068974431749720049/100000000000000000000000000)), ((159319997167449384989195311/200000000000000000000000000), (165692385068974431749720049/100000000000000000000000000)), ((159319997167449384989195311/200000000000000000000000000), (164692385068974431749720049/100000000000000000000000000)), ((248983/250000), (65635441/40000000)), ((248983/250000), (830121073/500000000)), ((469364497/500000000), (1687172101/1000000000)), ((868050603/1000000000), (1712569751/1000000000)), ((782691351/1000000000), (828328327/500000000)), ((790375591/1000000000), (1630323183/1000000000)), ((857991217/1000000000), (1586351539/1000000000)), ((471031633/500000000), (807848477/500000000))]

theorem sharedRosterCell04_owned (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell04, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell04, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point009_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point010_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point011_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP012] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point012_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell04_owned
