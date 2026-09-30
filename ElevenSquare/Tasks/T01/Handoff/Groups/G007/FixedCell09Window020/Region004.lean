import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region004_checked : region004.Check region004Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region004]
    · intro v hv
      simp only [region004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨region004p3, by simp [region004], region004p1, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [region004p3, region004p0, region004p1]
      · refine ⟨region004p0, by simp [region004], region004p2, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [region004p0, region004p1, region004p2]
      · refine ⟨region004p1, by simp [region004], region004p3, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [region004p1, region004p2, region004p3]
      · refine ⟨region004p2, by simp [region004], region004p0, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [region004p2, region004p3, region004p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region004, region004Feature, core, region004p0, region004p1, region004p2, region004p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window020
