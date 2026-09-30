import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem core_checked : ∀ v ∈ core, BaselineCoreVertexCheck v inputRow.lo inputRow.hi := by
  intro v hv
  simp only [core, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell10Row022
