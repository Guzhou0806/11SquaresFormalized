import ElevenSquare.Tasks.T01.Field03Cell04Row000.Pair02Data

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair02Node004_checked : pair02Node004.Check pair02Source004 pair02Targets := by
  simp only [BaselineCoverCertificate.Check, BaselinePolygonImplicationCheck,
    BaselineImplicationCheck, BaselineStrictImplicationCheck, BaselineCombinationValid,
    pair02Node004, pair02Source004, pair02Targets, pair02Plan, region002, region009, r002p0, r002p1, r002p2, r002p3, r002p4, r002p5, r009p0, r009p1, r009p2, r009p3,
    List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.forall_mem_cons, List.forall_mem_nil, Prod.fst, Prod.snd]
  norm_num [baselineCombinationSum, baselineZeroHalfplane, baselineEdge, List.getD]
  all_goals
    repeat' apply And.intro
    all_goals
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
