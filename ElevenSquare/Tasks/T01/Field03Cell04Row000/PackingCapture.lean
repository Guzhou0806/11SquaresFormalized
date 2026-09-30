import ElevenSquare.Tasks.T01.Field03Cell04Row000.CheckedRow
import ElevenSquare.Tasks.T01.CornerSeed005

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The complete first field-03 interval, for actual contained, non-overlapping
squares assigned to cells 4 and 0. There is no geometric certificate premise. -/
theorem capture_from_packing (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : (P.squares i).axis = chartAxis t)
    (hl : (0 : ℝ) ≤ t) (hu : t ≤ (1/256 : ℝ)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  apply packing_row_majority P i
    (row_contains _ hcell (P.contained i) t ht0 ht1 ha hl hu)
  intro p hp
  have he : p = CornerSeed005.point := by
    simpa only [forbiddenPoints, CornerSeed005.point, List.mem_singleton] using hp
  subst p
  exact ⟨j, hij, CornerSeed005.point_owned _ hother (P.contained j) hchart⟩

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
