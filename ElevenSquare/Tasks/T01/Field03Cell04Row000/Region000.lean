import ElevenSquare.Tasks.T01.Field03Cell04Row000.Core

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region000_checked : region000.Check feature000 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region000]
    · intro v hv
      simp only [region000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨r000p5, by simp [region000], r000p1, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p5, r000p0, r000p1]
      · refine ⟨r000p0, by simp [region000], r000p2, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p0, r000p1, r000p2]
      · refine ⟨r000p1, by simp [region000], r000p3, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p1, r000p2, r000p3]
      · refine ⟨r000p2, by simp [region000], r000p4, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p2, r000p3, r000p4]
      · refine ⟨r000p3, by simp [region000], r000p5, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p3, r000p4, r000p5]
      · refine ⟨r000p4, by simp [region000], r000p0, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p4, r000p5, r000p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region000, feature000, core, r000p0, r000p1, r000p2, r000p3, r000p4, r000p5, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
