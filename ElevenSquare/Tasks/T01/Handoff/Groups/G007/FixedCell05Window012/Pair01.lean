import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem pair01_checked : pair01.Check pair01Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [pair01]
    · intro v hv
      simp only [pair01, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨pair01p5, by simp [pair01], pair01p1, by simp [pair01],
          by simp [pair01], by simp [pair01], ?_⟩
        norm_num [pair01p5, pair01p0, pair01p1]
      · refine ⟨pair01p0, by simp [pair01], pair01p2, by simp [pair01],
          by simp [pair01], by simp [pair01], ?_⟩
        norm_num [pair01p0, pair01p1, pair01p2]
      · refine ⟨pair01p1, by simp [pair01], pair01p3, by simp [pair01],
          by simp [pair01], by simp [pair01], ?_⟩
        norm_num [pair01p1, pair01p2, pair01p3]
      · refine ⟨pair01p2, by simp [pair01], pair01p4, by simp [pair01],
          by simp [pair01], by simp [pair01], ?_⟩
        norm_num [pair01p2, pair01p3, pair01p4]
      · refine ⟨pair01p3, by simp [pair01], pair01p5, by simp [pair01],
          by simp [pair01], by simp [pair01], ?_⟩
        norm_num [pair01p3, pair01p4, pair01p5]
      · refine ⟨pair01p4, by simp [pair01], pair01p0, by simp [pair01],
          by simp [pair01], by simp [pair01], ?_⟩
        norm_num [pair01p4, pair01p5, pair01p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, pair01, pair01Feature, core, pair01p0, pair01p1, pair01p2, pair01p3, pair01p4, pair01p5, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05Window012
