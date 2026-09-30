import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_cell05 (q : UnitSquare)
    (hcell : ClosedCell 5 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ v ∈ ownedRosterCell05, OpenSquare q (realPoint v) := by
  intro v hv
  simp only [ownedRosterCell05, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP7] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point007_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.ownedP8] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell05.gate_point008_owned q hcell)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
