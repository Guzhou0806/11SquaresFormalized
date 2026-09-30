import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem medianToPair01_checked :
    BaselinePolygonImplicationCheck medianTarget pair01.polygon medianToPair01 := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    medianToPair01, medianTarget, pair01, baselineEdge, List.getD, pair01p0, pair01p1, pair01p2, pair01p3, pair01p4, pair01p5]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window001
