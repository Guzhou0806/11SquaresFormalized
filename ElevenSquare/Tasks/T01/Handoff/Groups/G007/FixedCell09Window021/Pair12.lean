import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair12_checked : pair12.Check pair12Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [pair12]
    · intro v hv
      simp only [pair12, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨pair12p5, by simp [pair12], pair12p1, by simp [pair12],
          by simp [pair12], by simp [pair12], ?_⟩
        norm_num [pair12p5, pair12p0, pair12p1]
      · refine ⟨pair12p0, by simp [pair12], pair12p2, by simp [pair12],
          by simp [pair12], by simp [pair12], ?_⟩
        norm_num [pair12p0, pair12p1, pair12p2]
      · refine ⟨pair12p1, by simp [pair12], pair12p3, by simp [pair12],
          by simp [pair12], by simp [pair12], ?_⟩
        norm_num [pair12p1, pair12p2, pair12p3]
      · refine ⟨pair12p2, by simp [pair12], pair12p4, by simp [pair12],
          by simp [pair12], by simp [pair12], ?_⟩
        norm_num [pair12p2, pair12p3, pair12p4]
      · refine ⟨pair12p3, by simp [pair12], pair12p5, by simp [pair12],
          by simp [pair12], by simp [pair12], ?_⟩
        norm_num [pair12p3, pair12p4, pair12p5]
      · refine ⟨pair12p4, by simp [pair12], pair12p0, by simp [pair12],
          by simp [pair12], by simp [pair12], ?_⟩
        norm_num [pair12p4, pair12p5, pair12p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, pair12, pair12Feature, core, pair12p0, pair12p1, pair12p2, pair12p3, pair12p4, pair12p5, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window021
