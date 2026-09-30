import ElevenSquare.Tasks.T01.Field03Cell04Row003.Data

namespace ElevenSquare.Tasks.T01.Field03Cell04Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem source_matches : baselineSlab 4 margin = source := by
  change baselineSlab ⟨4, by decide⟩ margin = source
  norm_num [baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, margin, source, List.finRange]

theorem wall_checked : BaselineWallCheck (3/256) (1/64) margin := by
  norm_num [BaselineWallCheck, margin]

theorem row_contains (q : UnitSquare)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : ((3/256) : ℝ) ≤ t) (hu : t ≤ ((1/64) : ℝ)) : inputRow.contains q := by
  refine ⟨?_, t, ht0, ht1, ?_, ?_, ha⟩
  · change q.center ∈ source.carrier
    rw [← source_matches]
    exact baseline_slab_contains q 4 (3/256) (1/64) margin t wall_checked (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu) ha hcont
      (baselineCellPolygon_contains hcell)
  · simpa [inputRow] using hl
  · simpa [inputRow] using hu

end
end ElevenSquare.Tasks.T01.Field03Cell04Row003

namespace ElevenSquare.Tasks.T01.Field03Cell04Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem core_checked : ∀ v ∈ core, BaselineCoreVertexCheck v inputRow.lo inputRow.hi := by
  intro v hv
  simp only [core, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row003

namespace ElevenSquare.Tasks.T01.Field03Cell04Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region000_checked : region000.Check feature000 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region000]
    · intro v hv
      simp only [region000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨r000p5, by simp [region000], r000p1, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p5, r000p0, r000p1]
      · refine ⟨r000p0, by simp [region000], r000p2, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p0, r000p1, r000p2]
      · refine ⟨r000p1, by simp [region000], r000p3, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p1, r000p2, r000p3]
      · refine ⟨r000p2, by simp [region000], r000p4, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p2, r000p3, r000p4]
      · refine ⟨r000p3, by simp [region000], r000p5, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p3, r000p4, r000p5]
      · refine ⟨r000p4, by simp [region000], r000p0, by simp [region000],
          by simp [region000], by simp [region000], ?_⟩
        norm_num [r000p4, r000p5, r000p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region000, feature000, core, r000p0, r000p1, r000p2, r000p3, r000p4, r000p5, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row003

namespace ElevenSquare.Tasks.T01.Field03Cell04Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region001_checked : region001.Check feature001 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region001]
    · intro v hv
      simp only [region001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨r001p5, by simp [region001], r001p1, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p5, r001p0, r001p1]
      · refine ⟨r001p0, by simp [region001], r001p2, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p0, r001p1, r001p2]
      · refine ⟨r001p1, by simp [region001], r001p3, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p1, r001p2, r001p3]
      · refine ⟨r001p2, by simp [region001], r001p4, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p2, r001p3, r001p4]
      · refine ⟨r001p3, by simp [region001], r001p5, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p3, r001p4, r001p5]
      · refine ⟨r001p4, by simp [region001], r001p0, by simp [region001],
          by simp [region001], by simp [region001], ?_⟩
        norm_num [r001p4, r001p5, r001p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region001, feature001, core, r001p0, r001p1, r001p2, r001p3, r001p4, r001p5, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row003

namespace ElevenSquare.Tasks.T01.Field03Cell04Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region002_checked : region002.Check feature002 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region002]
    · intro v hv
      simp only [region002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨r002p5, by simp [region002], r002p1, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p5, r002p0, r002p1]
      · refine ⟨r002p0, by simp [region002], r002p2, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p0, r002p1, r002p2]
      · refine ⟨r002p1, by simp [region002], r002p3, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p1, r002p2, r002p3]
      · refine ⟨r002p2, by simp [region002], r002p4, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p2, r002p3, r002p4]
      · refine ⟨r002p3, by simp [region002], r002p5, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p3, r002p4, r002p5]
      · refine ⟨r002p4, by simp [region002], r002p0, by simp [region002],
          by simp [region002], by simp [region002], ?_⟩
        norm_num [r002p4, r002p5, r002p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region002, feature002, core, r002p0, r002p1, r002p2, r002p3, r002p4, r002p5, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row003

namespace ElevenSquare.Tasks.T01.Field03Cell04Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region009_checked : region009.Check feature009 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region009]
    · intro v hv
      simp only [region009, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r009p3, by simp [region009], r009p1, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p3, r009p0, r009p1]
      · refine ⟨r009p0, by simp [region009], r009p2, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p0, r009p1, r009p2]
      · refine ⟨r009p1, by simp [region009], r009p3, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p1, r009p2, r009p3]
      · refine ⟨r009p2, by simp [region009], r009p0, by simp [region009],
          by simp [region009], by simp [region009], ?_⟩
        norm_num [r009p2, r009p3, r009p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region009, feature009, core, r009p0, r009p1, r009p2, r009p3, List.getD]

end
end ElevenSquare.Tasks.T01.Field03Cell04Row003
