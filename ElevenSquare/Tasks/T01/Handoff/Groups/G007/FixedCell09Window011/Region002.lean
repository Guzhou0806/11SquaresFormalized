import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window011.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window011
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region002_checked : region002.Check region002Feature inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region002]
    · intro v hv
      simp only [region002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨region002p3, by simp [region002], region002p1, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [region002p3, region002p0, region002p1]
      · refine ⟨region002p0, by simp [region002], region002p2, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [region002p0, region002p1, region002p2]
      · refine ⟨region002p1, by simp [region002], region002p3, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [region002p1, region002p2, region002p3]
      · refine ⟨region002p2, by simp [region002], region002p0, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [region002p2, region002p3, region002p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region002, region002Feature, core, region002p0, region002p1, region002p2, region002p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09Window011
