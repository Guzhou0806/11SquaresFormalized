import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window068.CoverData

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window068
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node005_checked : node005.Check nodeSource005 targets := by
  simp only [BaselineCoverCertificate.Check, BaselinePolygonImplicationCheck,
    BaselineImplicationCheck, BaselineStrictImplicationCheck, BaselineCombinationValid,
    node005, nodeSource005, targets, medianTarget0, medianTarget1,
    List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.forall_mem_cons, List.forall_mem_nil, Prod.fst, Prod.snd]
  norm_num [baselineCombinationSum, baselineZeroHalfplane, baselineEdge, List.getD]
  all_goals
    repeat' apply And.intro
    all_goals
      rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window068
