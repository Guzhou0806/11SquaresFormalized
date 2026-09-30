import ElevenSquare.Tasks.T01.Field03Cell04Row000.Core

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region001_checked : region001.Check feature001 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region001]
    · intro v hv
      simp only [region001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨r001p5, by simp [region001], r001p1, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p5, r001p0, r001p1]
      · refine ⟨r001p0, by simp [region001], r001p2, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p0, r001p1, r001p2]
      · refine ⟨r001p1, by simp [region001], r001p3, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p1, r001p2, r001p3]
      · refine ⟨r001p2, by simp [region001], r001p4, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p2, r001p3, r001p4]
      · refine ⟨r001p3, by simp [region001], r001p5, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p3, r001p4, r001p5]
      · refine ⟨r001p4, by simp [region001], r001p0, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p4, r001p5, r001p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region001, feature001, core, r001p0, r001p1, r001p2, r001p3, r001p4, r001p5, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
