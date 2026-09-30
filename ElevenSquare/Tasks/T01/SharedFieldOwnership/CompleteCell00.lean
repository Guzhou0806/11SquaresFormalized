import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.Ownership

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete normalized original gate roster for cell 0. -/
def sharedRosterCell00 : List QPoint := [((80206788320008528328995421/100000000000000000000000000), (176483527032089485245355847/200000000000000000000000000)), ((80706788320008528328995421/100000000000000000000000000), (176483527032089485245355847/200000000000000000000000000)), ((79706788320008528328995421/100000000000000000000000000), (176483527032089485245355847/200000000000000000000000000)), ((80206788320008528328995421/100000000000000000000000000), (177483527032089485245355847/200000000000000000000000000)), ((80206788320008528328995421/100000000000000000000000000), (175483527032089485245355847/200000000000000000000000000)), ((498020679/500000000), (872404559/1000000000)), ((498020679/500000000), (997648353/1000000000)), ((386169321/500000000), (997648353/1000000000)), ((158263411/200000000), (437530073/500000000)), ((175226227/200000000), (410961817/500000000)), ((37415093/40000000), (843701669/1000000000))]

theorem sharedRosterCell00_owned (q : UnitSquare)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ p ∈ sharedRosterCell00, OpenSquare q (realPoint p) := by
  intro p hp
  simp only [sharedRosterCell00, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.gate_point007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.ownedP5] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell00.gate_point008_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.ownedP009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.gate_point009_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.ownedP010] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell00.gate_point010_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership

#print axioms ElevenSquare.Tasks.T01.SharedFieldOwnership.sharedRosterCell00_owned
