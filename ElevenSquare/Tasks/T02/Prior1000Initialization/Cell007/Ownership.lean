import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell007.Geometry

namespace ElevenSquare.Tasks.T02.Prior1000Initialization.Cell007
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

theorem disk_points_checked : ∀ p ∈ diskOwned, DiskPointCheck vertices p := by
  intro p hp
  simp only [diskOwned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  all_goals norm_num [DiskPointCheck, vertices, p0, p1, p2, p3, p4, ownedP3]

/-- Checked archived subset; the remaining archived points require wall geometry. -/
theorem disk_hull_owned (q : UnitSquare)
    (hq : ClosedCell 7 (normalizeCenter q.center)) :
    rationalHull diskOwned ⊆ {p | OpenSquare q p} :=
  disk_cell_owned_hull 7 vertices diskOwned polygon implications cover_checked polygon_checked disk_points_checked q hq

end
end ElevenSquare.Tasks.T02.Prior1000Initialization.Cell007
