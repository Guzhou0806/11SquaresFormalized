import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_cell14 (q : UnitSquare)
    (hcell : ClosedCell 14 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ v ∈ ownedRosterCell14, OpenSquare q (realPoint v) := by
  intro v hv
  simp only [ownedRosterCell14, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP2] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point002_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.originalP14_005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.mirror_cell14_gate005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.originalP14_009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell01.mirror_cell14_gate009_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
