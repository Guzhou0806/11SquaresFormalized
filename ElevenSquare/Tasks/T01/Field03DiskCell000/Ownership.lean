import ElevenSquare.Tasks.T01.Field03DiskCell000.Geometry

namespace ElevenSquare.Tasks.T01.Field03DiskCell000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem points_checked : ∀ p ∈ owned, DiskPointCheck vertices p := by
  intro p hp
  simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [DiskPointCheck, vertices, p0, p1, p2, p3, p4, ownedP0, ownedP1, ownedP2, ownedP3, ownedP4, ownedP5]

/-- The selected archived field03 disk seeds for cell 0, for arbitrary orientations. -/
theorem initial_hull_owned (q : UnitSquare)
    (hq : ClosedCell 0 (normalizeCenter q.center)) :
    rationalHull owned ⊆ {p | OpenSquare q p} :=
  disk_cell_owned_hull 0 vertices owned polygon implications cover_checked polygon_checked points_checked q hq

end
end ElevenSquare.Tasks.T01.Field03DiskCell000
