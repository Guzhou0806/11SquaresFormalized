import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_cell11 (q : UnitSquare)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ v ∈ ownedRosterCell11, OpenSquare q (realPoint v) := by
  intro v hv
  simp only [ownedRosterCell11, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.originalP11_009] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.mirror_cell11_gate009_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
