import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region001_checked : region001.Check region001Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region001]
    · intro v hv
      simp only [region001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨region001p3, by simp [region001], region001p1, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [region001p3, region001p0, region001p1]
      · refine ⟨region001p0, by simp [region001], region001p2, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [region001p0, region001p1, region001p2]
      · refine ⟨region001p1, by simp [region001], region001p3, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [region001p1, region001p2, region001p3]
      · refine ⟨region001p2, by simp [region001], region001p0, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [region001p2, region001p3, region001p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region001, region001Feature, core, region001p0, region001p1, region001p2, region001p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004
