import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 6. -/
def sharedRosterCell06 : List QPoint := [((232768749014712286583541867/100000000000000000000000000), (67877260313210648443197979/40000000000000000000000000)), ((233268749014712286583541867/100000000000000000000000000), (67877260313210648443197979/40000000000000000000000000)), ((232268749014712286583541867/100000000000000000000000000), (67877260313210648443197979/40000000000000000000000000)), ((232768749014712286583541867/100000000000000000000000000), (68077260313210648443197979/40000000000000000000000000)), ((232768749014712286583541867/100000000000000000000000000), (67677260313210648443197979/40000000000000000000000000)), ((1170686087/500000000), (1702055787/1000000000)), ((2327777477/1000000000), (427931687/250000000)), ((46140627/20000000), (848529289/500000000)), ((2328225149/1000000000), (840840183/500000000)), ((2338878059/1000000000), (844991681/500000000))]

theorem sharedRosterCell06_owned (q : UnitSquare)
    (hcell : ClosedCell 6 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell06, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell06, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point005_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP6] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point006_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP7] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point007_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP8] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point008_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.ownedP9] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell06.gate_point009_owned q hcell)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell06_owned
