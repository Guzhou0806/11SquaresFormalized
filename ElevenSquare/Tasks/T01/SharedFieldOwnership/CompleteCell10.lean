import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 10. -/
def sharedRosterCell10 : List QPoint := [((461847638325220313984683659/200000000000000000000000000), (247674919094620486836184977/100000000000000000000000000)), ((462847638325220313984683659/200000000000000000000000000), (247674919094620486836184977/100000000000000000000000000)), ((460847638325220313984683659/200000000000000000000000000), (247674919094620486836184977/100000000000000000000000000)), ((461847638325220313984683659/200000000000000000000000000), (248174919094620486836184977/100000000000000000000000000)), ((461847638325220313984683659/200000000000000000000000000), (247174919094620486836184977/100000000000000000000000000)), ((1161387793/500000000), (620562701/250000000)), ((2309054033/1000000000), (311501087/125000000)), ((2295214137/1000000000), (155070511/62500000)), ((2298407401/1000000000), (617377483/250000000)), ((144709803/62500000), (1228439679/500000000)), ((579392219/250000000), (2458515827/1000000000))]

theorem sharedRosterCell10_owned (q : UnitSquare)
    (hcell : ClosedCell 10 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell10, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell10, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point005_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP6] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point006_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP7] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point007_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP8] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point008_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP9] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point009_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.ownedP10] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.gate_point010_owned q hcell)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell10_owned
