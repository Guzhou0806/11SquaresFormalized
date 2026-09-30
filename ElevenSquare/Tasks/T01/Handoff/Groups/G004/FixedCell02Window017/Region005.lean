import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region005_checked : region005.Check region005Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region005]
    · intro v hv
      simp only [region005, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨region005p3, by simp [region005], region005p1, by simp [region005],
          by simp [region005], by simp [region005], ?_⟩
        norm_num [region005p3, region005p0, region005p1]
      · refine ⟨region005p0, by simp [region005], region005p2, by simp [region005],
          by simp [region005], by simp [region005], ?_⟩
        norm_num [region005p0, region005p1, region005p2]
      · refine ⟨region005p1, by simp [region005], region005p3, by simp [region005],
          by simp [region005], by simp [region005], ?_⟩
        norm_num [region005p1, region005p2, region005p3]
      · refine ⟨region005p2, by simp [region005], region005p0, by simp [region005],
          by simp [region005], by simp [region005], ?_⟩
        norm_num [region005p2, region005p3, region005p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region005, region005Feature, core, region005p0, region005p1, region005p2, region005p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02Window017
