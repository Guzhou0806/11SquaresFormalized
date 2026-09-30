import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region003_checked : region003.Check region003Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region003]
    · intro v hv
      simp only [region003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨region003p3, by simp [region003], region003p1, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [region003p3, region003p0, region003p1]
      · refine ⟨region003p0, by simp [region003], region003p2, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [region003p0, region003p1, region003p2]
      · refine ⟨region003p1, by simp [region003], region003p3, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [region003p1, region003p2, region003p3]
      · refine ⟨region003p2, by simp [region003], region003p0, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [region003p2, region003p3, region003p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region003, region003Feature, core, region003p0, region003p1, region003p2, region003p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window008
