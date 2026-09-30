import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem medianToPair02_checked :
    BaselinePolygonImplicationCheck medianTarget pair02.polygon medianToPair02 := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    medianToPair02, medianTarget, pair02, baselineEdge, List.getD, pair02p0, pair02p1, pair02p2, pair02p3, pair02p4, pair02p5]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001
