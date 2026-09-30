import ElevenSquare.Tasks.T01.Field03Cell04Row000.Core

namespace ElevenSquare.Tasks.T01.Field03Cell04Row000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region009_checked : region009.Check feature009 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region009]
    · intro v hv
      simp only [region009, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r009p3, by simp [region009], r009p1, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p3, r009p0, r009p1]
      · refine ⟨r009p0, by simp [region009], r009p2, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p0, r009p1, r009p2]
      · refine ⟨r009p1, by simp [region009], r009p3, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p1, r009p2, r009p3]
      · refine ⟨r009p2, by simp [region009], r009p0, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p2, r009p3, r009p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region009, feature009, core, r009p0, r009p1, r009p2, r009p3, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row000
