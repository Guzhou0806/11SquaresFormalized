import ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row045.Data

namespace ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row045
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

set_option maxRecDepth 100000

theorem polygon_checked : BaselinePolygonCheck retainedVertices retainedRow.centers := by
  constructor
  · simp [retainedVertices]
  · intro v hv
    simp only [retainedVertices, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · refine ⟨c4, by simp [retainedVertices], c1, by simp [retainedVertices], ?_, ?_, ?_⟩
      all_goals rational_decide
    · refine ⟨c0, by simp [retainedVertices], c2, by simp [retainedVertices], ?_, ?_, ?_⟩
      all_goals rational_decide
    · refine ⟨c1, by simp [retainedVertices], c3, by simp [retainedVertices], ?_, ?_, ?_⟩
      all_goals rational_decide
    · refine ⟨c2, by simp [retainedVertices], c4, by simp [retainedVertices], ?_, ?_, ?_⟩
      all_goals rational_decide
    · refine ⟨c3, by simp [retainedVertices], c0, by simp [retainedVertices], ?_, ?_, ?_⟩
      all_goals rational_decide

theorem offsets_checked : ∀ p ∈ freshVertices, ∀ c ∈ retainedVertices,
    BaselineCoreVertexCheck (p.1-c.1, p.2-c.2) retainedRow.lo retainedRow.hi := by
  intro p hp
  simp only [freshVertices, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rational_decide

theorem promoted_points_checked : ∀ p ∈ freshVertices,
    DirectPointCheck retainedRow retainedVertices p := by
  intro p hp
  exact ⟨polygon_checked, offsets_checked p hp⟩

end
end ElevenSquare.Tasks.T02.Prior1000Step000Ownership.Row045
