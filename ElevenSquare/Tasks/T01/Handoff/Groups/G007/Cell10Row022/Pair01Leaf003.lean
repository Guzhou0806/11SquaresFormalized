import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Pair01Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair01Node003_checked : pair01Node003.Check pair01Source003 pair01Targets := by
  simp only [BaselineCoverCertificate.Check, BaselinePolygonImplicationCheck,
    BaselineImplicationCheck, BaselineStrictImplicationCheck, BaselineCombinationValid,
    pair01Node003, pair01Source003, pair01Targets, pair01Plan, region003, region082, region092, r003p0, r003p1, r003p2, r003p3, r082p0, r082p1, r082p2, r082p3, r092p0, r092p1, r092p2, r092p3,
    List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.forall_mem_cons, List.forall_mem_nil, Prod.fst, Prod.snd]
  norm_num [baselineCombinationSum, baselineZeroHalfplane, baselineEdge, List.getD]
  all_goals
    repeat' apply And.intro
    all_goals
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
