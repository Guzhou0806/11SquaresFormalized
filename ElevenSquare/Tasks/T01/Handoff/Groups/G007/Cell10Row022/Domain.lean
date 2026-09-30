import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Data
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.WallPose

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem wall_pose_checked : Candidate.WallPoseRowCheck 10 inputRow margin := by
  constructor
  · change source = baselineSlab ⟨10, by decide⟩ margin
    apply Eq.symm
    norm_num [baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
      baselineRationalSite, baselineRationalCap, margin, source, List.finRange]
  · norm_num [inputRow, Candidate.WallPoseRowCheck, BaselineWallCheck, margin]

theorem row_contains (q : UnitSquare)
    (hcell : ClosedCell 10 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : ((11/16) : ℝ) ≤ t) (hu : t ≤ ((23/32) : ℝ)) : inputRow.contains q := by
  exact Candidate.wall_pose_row_contains q 10 inputRow margin wall_pose_checked hcell hcont
    t ht0 ht1 ha (by simpa [inputRow] using hl) (by simpa [inputRow] using hu)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
