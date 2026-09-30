import ElevenSquare.Tasks.T01.Field03DiskCell000.Ownership

namespace ElevenSquare.Tasks.T01.Field03DiskCell000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Each selected point is owned without any orientation assumption. -/
theorem selected_point_owned (q : UnitSquare)
    (hcell : ClosedCell 0 (normalizeCenter q.center)) (p : QPoint)
    (hp : p ∈ owned) : OpenSquare q (realPoint p) := by
  apply initial_hull_owned q hcell
  apply subset_convexHull ℝ _
  exact ⟨p, hp, rfl⟩

end
end ElevenSquare.Tasks.T01.Field03DiskCell000
