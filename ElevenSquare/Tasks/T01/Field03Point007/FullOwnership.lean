import ElevenSquare.Tasks.T01.Field03Point007.Ownership
import ElevenSquare.Tasks.T01.Field03Point007Early.Ownership

namespace ElevenSquare.Tasks.T01.Field03Point007.FullOwnership
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The archived point belongs to every contained square in cell 0,
including both ends of the orientation chart. -/
theorem point_owned (q : UnitSquare)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint Field03Point007.point) := by
  obtain ⟨t, ht0, ht1, ha⟩ := hchart
  by_cases hcut : t ≤ (3/64 : ℝ)
  · have h := Field03Point007Early.point_owned q hcell hcont ⟨t, ht0, hcut, ha⟩
    simpa [Field03Point007Early.point, Field03Point007.point] using h
  · exact Field03Point007.point_owned q hcell hcont
      ⟨t, le_of_not_ge hcut, ht1, ha⟩

end
end ElevenSquare.Tasks.T01.Field03Point007.FullOwnership
