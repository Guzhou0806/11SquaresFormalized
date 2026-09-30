import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region082_checked : region082.Check feature082 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region082]
    · intro v hv
      simp only [region082, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r082p3, by simp [region082], r082p1, by simp [region082],
          by simp [region082], by simp [region082], ?_⟩
        norm_num [r082p3, r082p0, r082p1]
      · refine ⟨r082p0, by simp [region082], r082p2, by simp [region082],
          by simp [region082], by simp [region082], ?_⟩
        norm_num [r082p0, r082p1, r082p2]
      · refine ⟨r082p1, by simp [region082], r082p3, by simp [region082],
          by simp [region082], by simp [region082], ?_⟩
        norm_num [r082p1, r082p2, r082p3]
      · refine ⟨r082p2, by simp [region082], r082p0, by simp [region082],
          by simp [region082], by simp [region082], ?_⟩
        norm_num [r082p2, r082p3, r082p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region082, feature082, core, r082p0, r082p1, r082p2, r082p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
