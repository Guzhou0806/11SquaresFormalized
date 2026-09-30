import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001.Data
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.WallPose

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem wall_pose_checked : Candidate.WallPoseRowCheck 5 inputRow margin := by
  constructor
  · change source = baselineSlab ⟨5, by decide⟩ margin
    apply Eq.symm
    norm_num [baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
      baselineRationalSite, baselineRationalCap, margin, source, List.finRange]
  · norm_num [inputRow, Candidate.WallPoseRowCheck, BaselineWallCheck, margin]

theorem row_contains (q : UnitSquare)
    (hcell : ClosedCell 5 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : ((1/32) : ℝ) ≤ t) (hu : t ≤ ((1/16) : ℝ)) : inputRow.contains q := by
  exact Candidate.wall_pose_row_contains q 5 inputRow margin wall_pose_checked hcell hcont
    t ht0 ht1 ha (by simpa [inputRow] using hl) (by simpa [inputRow] using hu)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem core_checked : ∀ v ∈ core, BaselineCoreVertexCheck v inputRow.lo inputRow.hi := by
  intro v hv
  simp only [core, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals norm_num [inputRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
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
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
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
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
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
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region004_checked : region004.Check feature004 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region004]
    · intro v hv
      simp only [region004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r004p3, by simp [region004], r004p1, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [r004p3, r004p0, r004p1]
      · refine ⟨r004p0, by simp [region004], r004p2, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [r004p0, r004p1, r004p2]
      · refine ⟨r004p1, by simp [region004], r004p3, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [r004p1, r004p2, r004p3]
      · refine ⟨r004p2, by simp [region004], r004p0, by simp [region004],
          by simp [region004], by simp [region004], ?_⟩
        norm_num [r004p2, r004p3, r004p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region004, feature004, core, r004p0, r004p1, r004p2, r004p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region010_checked : region010.Check feature010 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region010]
    · intro v hv
      simp only [region010, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r010p3, by simp [region010], r010p1, by simp [region010],
          by simp [region010], by simp [region010], ?_⟩
        norm_num [r010p3, r010p0, r010p1]
      · refine ⟨r010p0, by simp [region010], r010p2, by simp [region010],
          by simp [region010], by simp [region010], ?_⟩
        norm_num [r010p0, r010p1, r010p2]
      · refine ⟨r010p1, by simp [region010], r010p3, by simp [region010],
          by simp [region010], by simp [region010], ?_⟩
        norm_num [r010p1, r010p2, r010p3]
      · refine ⟨r010p2, by simp [region010], r010p0, by simp [region010],
          by simp [region010], by simp [region010], ?_⟩
        norm_num [r010p2, r010p3, r010p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region010, feature010, core, r010p0, r010p1, r010p2, r010p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region014_checked : region014.Check feature014 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region014]
    · intro v hv
      simp only [region014, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r014p3, by simp [region014], r014p1, by simp [region014],
          by simp [region014], by simp [region014], ?_⟩
        norm_num [r014p3, r014p0, r014p1]
      · refine ⟨r014p0, by simp [region014], r014p2, by simp [region014],
          by simp [region014], by simp [region014], ?_⟩
        norm_num [r014p0, r014p1, r014p2]
      · refine ⟨r014p1, by simp [region014], r014p3, by simp [region014],
          by simp [region014], by simp [region014], ?_⟩
        norm_num [r014p1, r014p2, r014p3]
      · refine ⟨r014p2, by simp [region014], r014p0, by simp [region014],
          by simp [region014], by simp [region014], ?_⟩
        norm_num [r014p2, r014p3, r014p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region014, feature014, core, r014p0, r014p1, r014p2, r014p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem region037_checked : region037.Check feature037 inputRow := by
  refine ⟨?_, ?_, core_checked⟩
  · constructor
    · simp [region037]
    · intro v hv
      simp only [region037, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine ⟨r037p3, by simp [region037], r037p1, by simp [region037],
          by simp [region037], by simp [region037], ?_⟩
        norm_num [r037p3, r037p0, r037p1]
      · refine ⟨r037p0, by simp [region037], r037p2, by simp [region037],
          by simp [region037], by simp [region037], ?_⟩
        norm_num [r037p0, r037p1, r037p2]
      · refine ⟨r037p1, by simp [region037], r037p3, by simp [region037],
          by simp [region037], by simp [region037], ?_⟩
        norm_num [r037p1, r037p2, r037p3]
      · refine ⟨r037p2, by simp [region037], r037p0, by simp [region037],
          by simp [region037], by simp [region037], ?_⟩
        norm_num [r037p2, r037p3, r037p0]
  · norm_num [DifferenceVerticesCheck, DifferenceWitness.Valid, DifferenceWitness.eval,
      HullWitness.Valid, HullWitness.eval, rationalMix, region037, feature037, core, r037p0, r037p1, r037p2, r037p3, List.getD]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.Cell05Row001
