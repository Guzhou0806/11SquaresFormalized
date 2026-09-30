import ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem cover_checked : BaselinePolygonImplicationCheck (baselineCellPolygon 10) polygon implications := by
  rw [source_matches]
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    source, polygon, implications, baselineEdge, List.getD, c0, c1, c2, c3, c4, c5]

theorem polygon_checked : BaselinePolygonCheck vertices polygon := by
  constructor
  · simp [vertices]
  · intro v hv
    simp only [vertices, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨c5, by simp [vertices], c1, by simp [vertices],
        by simp [polygon], by simp [polygon], ?_⟩
      norm_num [c5, c0, c1]
    · refine ⟨c0, by simp [vertices], c2, by simp [vertices],
        by simp [polygon], by simp [polygon], ?_⟩
      norm_num [c0, c1, c2]
    · refine ⟨c1, by simp [vertices], c3, by simp [vertices],
        by simp [polygon], by simp [polygon], ?_⟩
      norm_num [c1, c2, c3]
    · refine ⟨c2, by simp [vertices], c4, by simp [vertices],
        by simp [polygon], by simp [polygon], ?_⟩
      norm_num [c2, c3, c4]
    · refine ⟨c3, by simp [vertices], c5, by simp [vertices],
        by simp [polygon], by simp [polygon], ?_⟩
      norm_num [c3, c4, c5]
    · refine ⟨c4, by simp [vertices], c0, by simp [vertices],
        by simp [polygon], by simp [polygon], ?_⟩
      norm_num [c4, c5, c0]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.DiskCell10
