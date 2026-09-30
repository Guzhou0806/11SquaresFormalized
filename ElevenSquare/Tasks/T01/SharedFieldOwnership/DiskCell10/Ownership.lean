import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.Geometry

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem points_checked : ∀ p ∈ owned, DiskPointCheck vertices p := by
  intro p hp
  simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [DiskPointCheck, vertices, c0, c1, c2, c3, c4, c5, ownedP0, ownedP1, ownedP2, ownedP3, ownedP4, ownedP5, ownedP6, ownedP7, ownedP8, ownedP9, ownedP10]

/-- Strict full-chart ownership for the disk-bound points of cell 10. -/
theorem initial_hull_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    rationalHull owned ⊆ {p | OpenSquare q p} :=
  disk_cell_owned_hull 10 vertices owned polygon implications
    cover_checked polygon_checked points_checked q hq

theorem selected_point_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center))
    (p : QPoint) (hp : p ∈ owned) : OpenSquare q (realPoint p) := by
  apply initial_hull_owned q hq
  exact subset_convexHull ℝ _ ⟨p, hp, rfl⟩

/-- The point indexed 0 in the archived cell 10 gate. -/
theorem gate_point000_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP0) :=
  selected_point_owned q hq ownedP0 (by simp [owned])

/-- The point indexed 1 in the archived cell 10 gate. -/
theorem gate_point001_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP1) :=
  selected_point_owned q hq ownedP1 (by simp [owned])

/-- The point indexed 2 in the archived cell 10 gate. -/
theorem gate_point002_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP2) :=
  selected_point_owned q hq ownedP2 (by simp [owned])

/-- The point indexed 3 in the archived cell 10 gate. -/
theorem gate_point003_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP3) :=
  selected_point_owned q hq ownedP3 (by simp [owned])

/-- The point indexed 4 in the archived cell 10 gate. -/
theorem gate_point004_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP4) :=
  selected_point_owned q hq ownedP4 (by simp [owned])

/-- The point indexed 5 in the archived cell 10 gate. -/
theorem gate_point005_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP5) :=
  selected_point_owned q hq ownedP5 (by simp [owned])

/-- The point indexed 6 in the archived cell 10 gate. -/
theorem gate_point006_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP6) :=
  selected_point_owned q hq ownedP6 (by simp [owned])

/-- The point indexed 7 in the archived cell 10 gate. -/
theorem gate_point007_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP7) :=
  selected_point_owned q hq ownedP7 (by simp [owned])

/-- The point indexed 8 in the archived cell 10 gate. -/
theorem gate_point008_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP8) :=
  selected_point_owned q hq ownedP8 (by simp [owned])

/-- The point indexed 9 in the archived cell 10 gate. -/
theorem gate_point009_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP9) :=
  selected_point_owned q hq ownedP9 (by simp [owned])

/-- The point indexed 10 in the archived cell 10 gate. -/
theorem gate_point010_owned (q : UnitSquare)
    (hq : ClosedCell 10 (normalizeCenter q.center)) :
    OpenSquare q (realPoint ownedP10) :=
  selected_point_owned q hq ownedP10 (by simp [owned])

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10
