import ElevenSquare.Tasks.T01.Field03Cell04Row075.CheckedRow
import ElevenSquare.Tasks.T01.Field03DiskCell000.SelectedPoints
import ElevenSquare.Tasks.T01.Field03Point007.FullOwnership

namespace ElevenSquare.Tasks.T01.Field03Cell04Row075
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Closed archived row with forbidden points owned by the actual cell-zero square. -/
theorem capture_from_packing (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ (P.squares j).axis = chartAxis u)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : (P.squares i).axis = chartAxis t)
    (hl : ((23/32) : ℝ) ≤ t) (hu : t ≤ ((3/4) : ℝ)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  apply packing_row_majority P i
    (row_contains _ hcell (P.contained i) t ht0 ht1 ha hl hu)
  intro p hp
  simp only [forbiddenPoints, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · refine ⟨j, hij, ?_⟩
    apply Field03DiskCell000.selected_point_owned _ hother
    simp [Field03DiskCell000.owned, Field03DiskCell000.ownedP0]
  · refine ⟨j, hij, ?_⟩
    exact Field03Point007.FullOwnership.point_owned _ hother (P.contained j) hchart

end
end ElevenSquare.Tasks.T01.Field03Cell04Row075
