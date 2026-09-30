import ElevenSquare.Tasks.T01.Wall

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Exact finite input needed to put a wall-clipped slab in a pose row. -/
def WallPoseRowCheck (cell : Fin 16) (r : PoseRow) (margin : ℚ) : Prop :=
  r.centers = baselineSlab cell margin ∧
    BaselineWallCheck r.lo r.hi margin

/-- One continuous argument covers every closed angle in the certified row. -/
theorem wall_pose_row_contains (q : UnitSquare) (cell : Fin 16)
    (r : PoseRow) (margin : ℚ) (hc : WallPoseRowCheck cell r margin)
    (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : (r.lo : ℝ) ≤ t) (hu : t ≤ (r.hi : ℝ)) : r.contains q := by
  refine ⟨?_, t, ht0, ht1, hl, hu, ha⟩
  rw [hc.1]
  exact baseline_slab_contains q cell r.lo r.hi margin t hc.2 hl hu ha hcont
    (baselineCellPolygon_contains hcell)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.wall_pose_row_contains
