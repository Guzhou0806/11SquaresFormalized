import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair01Data

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair01Node003_checked : pair01Node003.Check pair01Source003 pair01Targets := by
  simp only [BaselineCoverCertificate.Check, BaselinePolygonImplicationCheck,
    BaselineImplicationCheck, BaselineStrictImplicationCheck, BaselineCombinationValid,
    pair01Node003, pair01Source003, pair01Targets, pair01Plan, region001, region009, r001p0, r001p1, r001p2, r001p3, r001p4, r001p5, r009p0, r009p1, r009p2, r009p3,
    List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.forall_mem_cons, List.forall_mem_nil, Prod.fst, Prod.snd]
  norm_num [baselineCombinationSum, baselineZeroHalfplane, baselineEdge, List.getD]
  all_goals
    repeat' apply And.intro
    all_goals
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
