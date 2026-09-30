import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017.CoverData

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node007_checked : node007.Check nodeSource007 targets := by
  simp only [BaselineCoverCertificate.Check, BaselinePolygonImplicationCheck,
    BaselineImplicationCheck, BaselineStrictImplicationCheck, BaselineCombinationValid,
    node007, nodeSource007, targets, medianTarget, region001, region001p0, region001p1, region001p2, region001p3, region002, region002p0, region002p1, region002p2, region002p3, region003, region003p0, region003p1, region003p2, region003p3, region004, region004p0, region004p1, region004p2, region004p3, region005, region005p0, region005p1, region005p2, region005p3,
    List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.forall_mem_cons, List.forall_mem_nil, Prod.fst, Prod.snd]
  norm_num [baselineCombinationSum, baselineZeroHalfplane, baselineEdge, List.getD]
  all_goals
    repeat' apply And.intro
    all_goals
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017
