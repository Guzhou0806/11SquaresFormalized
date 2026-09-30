import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12.Geometry

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem points_checked : ∀ p ∈ owned, DiskPointCheck vertices p := by
  intro p hp
  simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [DiskPointCheck, vertices, c0, c1, c2, c3, ownedP0, ownedP1, ownedP2, ownedP3, ownedP4]

/-- Strict full-chart ownership for the disk-bound points of cell 12. -/
theorem initial_hull_owned (q : UnitSquare)
    (hq : ClosedCell 12 (normalizeCenter q.center)) :
    rationalHull owned ⊆ {p | OpenSquare q p} :=
  disk_cell_owned_hull 12 vertices owned polygon implications
    cover_checked polygon_checked points_checked q hq

theorem selected_point_owned (q : UnitSquare)
    (hq : ClosedCell 12 (normalizeCenter q.center))
    (p : QPoint) (hp : p ∈ owned) : OpenSquare q (realPoint p) := by
  apply initial_hull_owned q hq
  exact subset_convexHull ℝ _ ⟨p, hp, rfl⟩

/-- The point indexed 0 in the archived cell 12 gate. -/
theorem gate_point000_owned (q : UnitSquare)
    (hq : ClosedCell 12 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP0) :=
  selected_point_owned q hq ownedP0 (by simp [owned])

/-- The point indexed 1 in the archived cell 12 gate. -/
theorem gate_point001_owned (q : UnitSquare)
    (hq : ClosedCell 12 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP1) :=
  selected_point_owned q hq ownedP1 (by simp [owned])

/-- The point indexed 2 in the archived cell 12 gate. -/
theorem gate_point002_owned (q : UnitSquare)
    (hq : ClosedCell 12 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP2) :=
  selected_point_owned q hq ownedP2 (by simp [owned])

/-- The point indexed 3 in the archived cell 12 gate. -/
theorem gate_point003_owned (q : UnitSquare)
    (hq : ClosedCell 12 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP3) :=
  selected_point_owned q hq ownedP3 (by simp [owned])

/-- The point indexed 4 in the archived cell 12 gate. -/
theorem gate_point004_owned (q : UnitSquare)
    (hq : ClosedCell 12 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP4) :=
  selected_point_owned q hq ownedP4 (by simp [owned])

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell12
