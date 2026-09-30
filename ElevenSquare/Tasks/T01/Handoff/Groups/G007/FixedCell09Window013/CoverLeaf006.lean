import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window013.CoverData

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window013
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node006_checked : node006.Check nodeSource006 targets := by
  simp only [BaselineCoverCertificate.Check, BaselinePolygonImplicationCheck,
    BaselineImplicationCheck, BaselineStrictImplicationCheck, BaselineCombinationValid,
    node006, nodeSource006, targets, medianTarget, pair01, pair01p0, pair01p1, pair01p2, pair01p3, pair01p4, pair01p5, pair02, pair02p0, pair02p1, pair02p2, pair02p3, pair02p4, pair02p5, pair12, pair12p0, pair12p1, pair12p2, pair12p3, pair12p4, pair12p5, region000, region000p0, region000p1, region000p2, region000p3, region002, region002p0, region002p1, region002p2, region002p3,
    List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.forall_mem_cons, List.forall_mem_nil, Prod.fst, Prod.snd]
  norm_num [baselineCombinationSum, baselineZeroHalfplane, baselineEdge, List.getD]
  all_goals
    repeat' apply And.intro
    all_goals
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window013
