import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair00Data

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair00Node004_checked : pair00Node004.Check pair00Source004 pair00Targets := by
  simp only [BaselineCoverCertificate.Check, BaselinePolygonImplicationCheck,
    BaselineImplicationCheck, BaselineStrictImplicationCheck, BaselineCombinationValid,
    pair00Node004, pair00Source004, pair00Targets, pair00Plan, region000, region009, r000p0, r000p1, r000p2, r000p3, r000p4, r000p5, r009p0, r009p1, r009p2, r009p3,
    List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.forall_mem_cons, List.forall_mem_nil, Prod.fst, Prod.snd]
  norm_num [baselineCombinationSum, baselineZeroHalfplane, baselineEdge, List.getD]
  all_goals
    repeat' apply And.intro
    all_goals
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
