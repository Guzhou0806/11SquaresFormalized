import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell000.Data

namespace ElevenSquare.Tasks.T02.Prior1000Initialization.Cell000
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

theorem cover_checked : BaselinePolygonImplicationCheck (baselineCellPolygon 0) polygon implications := by
  rw [source_matches]
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck, BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane, source, polygon, implications, baselineEdge, List.getD, p0, p1, p2, p3, p4]

theorem polygon_checked : BaselinePolygonCheck vertices polygon := by
  constructor
  · simp [vertices]
  · intro v hv
    simp only [vertices, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · refine ⟨p4, by simp [vertices], p1, by simp [vertices], by simp [polygon], by simp [polygon], ?_⟩
      norm_num [p4, p0, p1]
    · refine ⟨p0, by simp [vertices], p2, by simp [vertices], by simp [polygon], by simp [polygon], ?_⟩
      norm_num [p0, p1, p2]
    · refine ⟨p1, by simp [vertices], p3, by simp [vertices], by simp [polygon], by simp [polygon], ?_⟩
      norm_num [p1, p2, p3]
    · refine ⟨p2, by simp [vertices], p4, by simp [vertices], by simp [polygon], by simp [polygon], ?_⟩
      norm_num [p2, p3, p4]
    · refine ⟨p3, by simp [vertices], p0, by simp [vertices], by simp [polygon], by simp [polygon], ?_⟩
      norm_num [p3, p4, p0]

end
end ElevenSquare.Tasks.T02.Prior1000Initialization.Cell000
