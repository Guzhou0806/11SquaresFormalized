import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 3. -/
def sharedRosterCell03 : List QPoint := [((598058557561106414706741913/200000000000000000000000000), (19894392534717634717104431/25000000000000000000000000)), ((599058557561106414706741913/200000000000000000000000000), (19894392534717634717104431/25000000000000000000000000)), ((597058557561106414706741913/200000000000000000000000000), (19894392534717634717104431/25000000000000000000000000)), ((598058557561106414706741913/200000000000000000000000000), (20019392534717634717104431/25000000000000000000000000)), ((598058557561106414706741913/200000000000000000000000000), (19769392534717634717104431/25000000000000000000000000)), ((1537998631/500000000), (830458721/1000000000)), ((3033327231/1000000000), (486019933/500000000)), ((1511413727/500000000), (497957757/500000000)), ((1439673887/500000000), (497957757/500000000)), ((1439673887/500000000), (359788647/500000000)), ((1451239527/500000000), (706762123/1000000000)), ((3058261939/1000000000), (40587311/50000000))]

theorem sharedRosterCell03_owned (q : UnitSquare)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell03, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell03, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell03.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.gate_point007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.ownedP008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.gate_point008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.ownedP009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.gate_point009_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.ownedP010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.gate_point010_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.ownedP011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.gate_point011_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell03_owned
