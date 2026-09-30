import ElevenSquare.Tasks.T01.Field03Cell08Row353.CheckedRow
import ElevenSquare.Tasks.T01.SiteOwnership
import ElevenSquare.Tasks.T01.SharedFieldOwnership.SymbolicCell03.Ownership

namespace ElevenSquare.Tasks.T01.Field03Cell08Row353
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Exact closed cell-eight row, conditional on checked owner helpers. -/
theorem capture_from_packing (P : Packing 11 coverCap) (i j4 j12 : Owner)
    (hi4 : i ≠ j4) (hi12 : i ≠ j12)
    (hcell : ClosedCell 8 (normalizeCenter (P.squares i).center))
    (hcell4 : ClosedCell 4 (normalizeCenter (P.squares j4).center))
    (hcell12 : ClosedCell 12 (normalizeCenter (P.squares j12).center))
    (hchart12 : ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ (P.squares j12).axis = chartAxis u)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : (P.squares i).axis = chartAxis t)
    (hl : ((127/128) : ℝ) ≤ t) (hu : t ≤ (1 : ℝ)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  apply packing_row_majority P i
    (row_contains _ hcell (P.contained i) t ht0 ht1 ha hl hu)
  intro p hp
  simp only [forbiddenPoints, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  · refine ⟨j12, hi12, ?_⟩
    exact SharedFieldOwnership.SymbolicCell03.mirror_cell12_gate005_owned _ hcell12 (P.contained j12) hchart12

end
end ElevenSquare.Tasks.T01.Field03Cell08Row353
