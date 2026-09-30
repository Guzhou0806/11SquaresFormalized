import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 12. -/
def sharedRosterCell12 : List QPoint := [((177358160443456420755258087/200000000000000000000000000), (77032697215852719715645569/25000000000000000000000000)), ((178358160443456420755258087/200000000000000000000000000), (77032697215852719715645569/25000000000000000000000000)), ((176358160443456420755258087/200000000000000000000000000), (77032697215852719715645569/25000000000000000000000000)), ((177358160443456420755258087/200000000000000000000000000), (77157697215852719715645569/25000000000000000000000000)), ((177358160443456420755258087/200000000000000000000000000), (76907697215852719715645569/25000000000000000000000000)), ((124716977/125000000), (720292019/250000000)), ((124716977/125000000), (394688287/125000000)), ((121825567/125000000), (3170321467/1000000000)), ((818821651/1000000000), (306533737/100000000)), ((100135791/125000000), (3046624869/1000000000)), ((843756359/1000000000), (726260931/250000000)), ((106782017/125000000), (720292019/250000000))]

theorem sharedRosterCell12_owned (q : UnitSquare)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell12, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell12, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.originalP12_005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.originalP12_006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.originalP12_007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.originalP12_008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.originalP12_009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate009_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.originalP12_010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate010_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.originalP12_011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate011_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell12_owned
