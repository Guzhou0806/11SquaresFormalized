import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.CheckedRow
import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.Ownership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Ownership

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare Pending
noncomputable section

/-- Conditional packing-level result for this one closed angular interval.
    Occupancy supplies the two other owners and their closed cells. -/
theorem packing_row_choice_of_cells (P : Packing 11 coverCap)
    (hc : IsCharted P) (i j11 j14 : Owner)
    (hrow : inputRow.contains (P.squares i))
    (h11 : ClosedCell 11 (normalizeCenter (P.squares j11).center))
    (h14 : ClosedCell 14 (normalizeCenter (P.squares j14).center))
    (hi11 : i ≠ j11) (hi14 : i ≠ j14) :
    OpenSquare (P.squares i) (realPoint G007.point) ∨
      BaselineMajorityCapture G007.sites 2 (P.squares i) := by
  apply packing_row_choice P i hrow
  intro p hp
  simp only [forbiddenPoints, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · refine ⟨j11, hi11, ?_⟩
    simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.point] using
      (ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.point_owned
        (P.squares j11) h11 (P.contained j11) (hc j11))
  · refine ⟨j14, hi14, ?_⟩
    simpa [ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.ownedP4] using
      (ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell14.gate_point004_owned
        (P.squares j14) h14)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.packing_row_choice_of_cells
