import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem medianToPair12_checked :
    BaselinePolygonImplicationCheck medianTarget pair12.polygon medianToPair12 := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    medianToPair12, medianTarget, pair12, baselineEdge, List.getD, pair12p0, pair12p1, pair12p2, pair12p3, pair12p4, pair12p5]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window000
