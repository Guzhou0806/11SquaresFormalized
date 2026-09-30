import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region000_checked : region000.Check region000Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region000]
    · intro v hv
      simp only [region000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨region000p3, by simp [region000], region000p1, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [region000p3, region000p0, region000p1]
      · refine ⟨region000p0, by simp [region000], region000p2, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [region000p0, region000p1, region000p2]
      · refine ⟨region000p1, by simp [region000], region000p3, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [region000p1, region000p2, region000p3]
      · refine ⟨region000p2, by simp [region000], region000p0, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [region000p2, region000p3, region000p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region000, region000Feature, core, region000p0, region000p1, region000p2, region000p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015
