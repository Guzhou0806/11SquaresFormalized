import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 9. -/
def sharedRosterCell09 : List QPoint := [((154939609987569131147458133/100000000000000000000000000), (87206083287701918649202021/40000000000000000000000000)), ((155439609987569131147458133/100000000000000000000000000), (87206083287701918649202021/40000000000000000000000000)), ((154439609987569131147458133/100000000000000000000000000), (87206083287701918649202021/40000000000000000000000000)), ((154939609987569131147458133/100000000000000000000000000), (87406083287701918649202021/40000000000000000000000000)), ((154939609987569131147458133/100000000000000000000000000), (87006083287701918649202021/40000000000000000000000000)), ((19625653/12500000), (545006253/250000000)), ((1548858441/1000000000), (274425403/125000000)), ((1538205531/1000000000), (546775057/250000000)), ((191963927/125000000), (2175027803/1000000000)), ((1549306113/1000000000), (1082678421/500000000))]

theorem sharedRosterCell09_owned (q : UnitSquare)
    (hcell : ClosedCell 9 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell09, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell09, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point005_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP6] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point006_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP7] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point007_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP8] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point008_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.ownedP9] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell09.gate_point009_owned q hcell)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell09_owned
