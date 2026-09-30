import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 14. -/
def sharedRosterCell14 : List QPoint := [((115167512002955994035477669/50000000000000000000000000), (324616765542600606379986307/100000000000000000000000000)), ((115417512002955994035477669/50000000000000000000000000), (324616765542600606379986307/100000000000000000000000000)), ((114917512002955994035477669/50000000000000000000000000), (324616765542600606379986307/100000000000000000000000000)), ((115167512002955994035477669/50000000000000000000000000), (325116765542600606379986307/100000000000000000000000000)), ((115167512002955994035477669/50000000000000000000000000), (324116765542600606379986307/100000000000000000000000000)), ((2333200481/1000000000), (799588769/250000000)), ((2333200481/1000000000), (3247869439/1000000000)), ((577291079/250000000), (816532201/250000000)), ((2273446261/1000000000), (161859053/50000000)), ((2305035533/1000000000), (1474001781/500000000))]

theorem sharedRosterCell14_owned (q : UnitSquare)
    (hcell : ClosedCell 14 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell14, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell14, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.originalP14_005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.mirror_cell14_gate005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.originalP14_006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.mirror_cell14_gate006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point007_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.originalP14_008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.mirror_cell14_gate008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.originalP14_009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.mirror_cell14_gate009_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell14_owned
