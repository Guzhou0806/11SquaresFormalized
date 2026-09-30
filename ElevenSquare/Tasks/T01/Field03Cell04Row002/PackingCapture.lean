import ElevenSquare.Tasks.T01.Field03Cell04Row002.CheckedRow
import ElevenSquare.Tasks.T01.CornerSeed005
import ElevenSquare.Tasks.T01.SiteOwnership

namespace ElevenSquare.Tasks.T01.Field03Cell04Row002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Complete archived interval, with each ownership premise derived from the packing. -/
theorem capture_from_packing (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : (P.squares i).axis = chartAxis t)
    (hl : (1/128 : ℝ) ≤ t) (hu : t ≤ (3/256 : ℝ)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  apply packing_row_majority P i
    (row_contains _ hcell (P.contained i) t ht0 ht1 ha hl hu)
  intro p hp
  simp only [forbiddenPoints, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  · refine ⟨j, hij, ?_⟩
    exact CornerSeed005.point_owned _ hother (P.contained j) hchart

end
end ElevenSquare.Tasks.T01.Field03Cell04Row002
