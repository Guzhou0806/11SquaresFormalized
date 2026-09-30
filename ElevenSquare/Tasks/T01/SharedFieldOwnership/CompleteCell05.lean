import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 5. -/
def sharedRosterCell05 : List QPoint := [((313569079679342521477316341/200000000000000000000000000), (140033439907660930894815023/100000000000000000000000000)), ((314569079679342521477316341/200000000000000000000000000), (140033439907660930894815023/100000000000000000000000000)), ((312569079679342521477316341/200000000000000000000000000), (140033439907660930894815023/100000000000000000000000000)), ((313569079679342521477316341/200000000000000000000000000), (140533439907660930894815023/100000000000000000000000000)), ((313569079679342521477316341/200000000000000000000000000), (139533439907660930894815023/100000000000000000000000000)), ((1581869453/1000000000), (697977707/500000000)), ((1578676189/1000000000), (703786829/500000000)), ((780863371/500000000), (177525529/125000000)), ((779757357/500000000), (1418567763/1000000000)), ((388577001/250000000), (697416393/500000000)), ((1568029557/1000000000), (692537447/500000000))]

theorem sharedRosterCell05_owned (q : UnitSquare)
    (hcell : ClosedCell 5 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell05, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell05, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point005_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP6] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point006_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP7] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point007_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP8] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point008_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP9] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point009_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP10] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point010_owned q hcell)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell05_owned
