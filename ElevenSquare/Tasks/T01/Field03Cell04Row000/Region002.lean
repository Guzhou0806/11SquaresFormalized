import ElevenSquare.Tasks.T01.Field03Cell04Row000.Core

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region002_checked : region002.Check feature002 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region002]
    · intro v hv
      simp only [region002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨r002p5, by simp [region002], r002p1, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p5, r002p0, r002p1]
      · refine ⟨r002p0, by simp [region002], r002p2, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p0, r002p1, r002p2]
      · refine ⟨r002p1, by simp [region002], r002p3, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p1, r002p2, r002p3]
      · refine ⟨r002p2, by simp [region002], r002p4, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p2, r002p3, r002p4]
      · refine ⟨r002p3, by simp [region002], r002p5, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p3, r002p4, r002p5]
      · refine ⟨r002p4, by simp [region002], r002p0, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p4, r002p5, r002p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region002, feature002, core, r002p0, r002p1, r002p2, r002p3, r002p4, r002p5, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
