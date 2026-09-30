import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Core

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region003_checked : region003.Check feature003 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region003]
    · intro v hv
      simp only [region003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r003p3, by simp [region003], r003p1, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [r003p3, r003p0, r003p1]
      · refine ⟨r003p0, by simp [region003], r003p2, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [r003p0, r003p1, r003p2]
      · refine ⟨r003p1, by simp [region003], r003p3, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [r003p1, r003p2, r003p3]
      · refine ⟨r003p2, by simp [region003], r003p0, by simp [region003],
          by simp [region003], by simp [region003], ?_⟩
        norm_num [r003p2, r003p3, r003p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region003, feature003, core, r003p0, r003p1, r003p2, r003p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
