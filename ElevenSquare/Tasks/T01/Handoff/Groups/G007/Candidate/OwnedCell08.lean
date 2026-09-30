import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_cell08 (q : UnitSquare)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ v ∈ ownedRosterCell08, OpenSquare q (realPoint v) := by
  intro v hv
  simp only [ownedRosterCell08, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell08.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.originalP08_012] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell07.mirror_cell08_gate012_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
