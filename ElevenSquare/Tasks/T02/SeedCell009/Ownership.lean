import ElevenSquare.Tasks.T02.SeedCell009.Geometry

namespace ElevenSquare.Tasks.T02.SeedCell009
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

theorem points_checked : ∀ p ∈ owned, DiskPointCheck vertices p := by
  intro p hp
  simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [DiskPointCheck, vertices, p0, p1, p2, p3, p4, p5, ownedP0, ownedP1, ownedP2, ownedP3, ownedP4]

/-- The complete archived initial hull for cell 9, for arbitrary orientations. -/
theorem initial_hull_owned (q : UnitSquare)
    (hq : ClosedCell 9 (normalizeCenter q.center)) :
    rationalHull owned ⊆ {p | OpenSquare q p} :=
  disk_cell_owned_hull 9 vertices owned polygon implications cover_checked polygon_checked points_checked q hq

end
end ElevenSquare.Tasks.T02.SeedCell009
