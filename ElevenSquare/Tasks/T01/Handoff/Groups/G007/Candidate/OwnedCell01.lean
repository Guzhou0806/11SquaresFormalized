import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_cell01 (q : UnitSquare)
    (hcell : ClosedCell 1 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ v ∈ ownedRosterCell01, OpenSquare q (realPoint v) := by
  intro v hv
  simp only [ownedRosterCell01, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.ownedP3] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell01.gate_point003_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.gate_point006_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
