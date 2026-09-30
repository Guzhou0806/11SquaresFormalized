import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region092_checked : region092.Check feature092 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region092]
    · intro v hv
      simp only [region092, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r092p3, by simp [region092], r092p1, by simp [region092],
          by simp [region092], by simp [region092], ?_⟩
        norm_num [r092p3, r092p0, r092p1]
      · refine ⟨r092p0, by simp [region092], r092p2, by simp [region092],
          by simp [region092], by simp [region092], ?_⟩
        norm_num [r092p0, r092p1, r092p2]
      · refine ⟨r092p1, by simp [region092], r092p3, by simp [region092],
          by simp [region092], by simp [region092], ?_⟩
        norm_num [r092p1, r092p2, r092p3]
      · refine ⟨r092p2, by simp [region092], r092p0, by simp [region092],
          by simp [region092], by simp [region092], ?_⟩
        norm_num [r092p2, r092p3, r092p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region092, feature092, core, r092p0, r092p1, r092p2, r092p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
