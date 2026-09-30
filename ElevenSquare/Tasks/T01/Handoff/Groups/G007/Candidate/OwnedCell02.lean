import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_cell02 (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ v ∈ ownedRosterCell02, OpenSquare q (realPoint v) := by
  intro v hv
  simp only [ownedRosterCell02, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell02.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell02.gate_point007_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
