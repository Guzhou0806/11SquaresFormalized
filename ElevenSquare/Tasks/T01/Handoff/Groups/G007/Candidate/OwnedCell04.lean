import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRoster
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem owned_cell04 (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    ∀ v ∈ ownedRosterCell04, OpenSquare q (realPoint v) := by
  intro v hv
  simp only [ownedRosterCell04, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP0] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point000_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP1] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point001_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.ownedP4] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell04.gate_point004_owned q hcell)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP005] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point005_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP006] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point006_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP007] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point007_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP008] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point008_owned q hcell hcont hchart)
  · simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.ownedP011] using (ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell04.gate_point011_owned q hcell hcont hchart)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
