import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair02_checked : pair02.Check pair02Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [pair02]
    · intro v hv
      simp only [pair02, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨pair02p5, by simp [pair02], pair02p1, by simp [pair02],
          by simp [pair02], by simp [pair02], ?_⟩
        norm_num [pair02p5, pair02p0, pair02p1]
      · refine ⟨pair02p0, by simp [pair02], pair02p2, by simp [pair02],
          by simp [pair02], by simp [pair02], ?_⟩
        norm_num [pair02p0, pair02p1, pair02p2]
      · refine ⟨pair02p1, by simp [pair02], pair02p3, by simp [pair02],
          by simp [pair02], by simp [pair02], ?_⟩
        norm_num [pair02p1, pair02p2, pair02p3]
      · refine ⟨pair02p2, by simp [pair02], pair02p4, by simp [pair02],
          by simp [pair02], by simp [pair02], ?_⟩
        norm_num [pair02p2, pair02p3, pair02p4]
      · refine ⟨pair02p3, by simp [pair02], pair02p5, by simp [pair02],
          by simp [pair02], by simp [pair02], ?_⟩
        norm_num [pair02p3, pair02p4, pair02p5]
      · refine ⟨pair02p4, by simp [pair02], pair02p0, by simp [pair02],
          by simp [pair02], by simp [pair02], ?_⟩
        norm_num [pair02p4, pair02p5, pair02p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, pair02, pair02Feature, core, pair02p0, pair02p1, pair02p2, pair02p3, pair02p4, pair02p5, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window015
