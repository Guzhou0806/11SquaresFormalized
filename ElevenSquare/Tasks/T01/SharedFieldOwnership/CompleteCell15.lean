import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 15. -/
def sharedRosterCell15 : List QPoint := [((307501570682272889402004579/100000000000000000000000000), (598933190972473350216644153/200000000000000000000000000)), ((308001570682272889402004579/100000000000000000000000000), (598933190972473350216644153/200000000000000000000000000)), ((307001570682272889402004579/100000000000000000000000000), (598933190972473350216644153/200000000000000000000000000)), ((307501570682272889402004579/100000000000000000000000000), (599933190972473350216644153/200000000000000000000000000)), ((307501570682272889402004579/100000000000000000000000000), (597933190972473350216644153/200000000000000000000000000)), ((776186237/250000000), (2879435237/1000000000)), ((617153307/200000000), (600404689/200000000)), ((600190491/200000000), (763789989/250000000)), ((588341253/200000000), (3033381921/1000000000)), ((360130279/125000000), (3004679031/1000000000)), ((360130279/125000000), (2879435237/1000000000))]

theorem sharedRosterCell15_owned (q : UnitSquare)
    (hcell : ClosedCell 15 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell15, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell15, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.originalP15_005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.mirror_cell15_gate005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell15.gate_point006_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.originalP15_007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.mirror_cell15_gate007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.originalP15_008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.mirror_cell15_gate008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.originalP15_009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.mirror_cell15_gate009_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.originalP15_010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.mirror_cell15_gate010_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell15_owned
