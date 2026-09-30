import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf000p0 : QPoint := ((236937085552390045307244760797429/214568800000000000000000000000000), (1/2))
def leaf000p1 : QPoint := ((425686698199336901251185345901871/208335600000000000000000000000000), (1/2))
def leaf000p2 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf000p3 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))

def leaf000 : WallOwnershipLeaf where
  margin := (1/2)
  polygon := [baselineEdge leaf000p0 leaf000p1, baselineEdge leaf000p1 leaf000p2, baselineEdge leaf000p2 leaf000p3, baselineEdge leaf000p3 leaf000p0]
  vertices := [leaf000p0, leaf000p1, leaf000p2, leaf000p3]
  implications := [[(2, (104941635319463420435183291650401322631/111755799223200000000000000000000000000))], [(10, (7232400458038950139353955508939564041/7274540515879286100000000000000000000))], [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))], [(8, (58765614008656790127811118144773985747/61408536520165925600000000000000000000))]]

theorem leaf000_checked : leaf000.Check 1 [point] 0 (1/512) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf000, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf000, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf000p0, leaf000p1, leaf000p2, leaf000p3]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf000]
      · intro v hv
        simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · refine ⟨leaf000p3, by simp [leaf000], leaf000p1, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p3, leaf000p0, leaf000p1]
        · refine ⟨leaf000p0, by simp [leaf000], leaf000p2, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p0, leaf000p1, leaf000p2]
        · refine ⟨leaf000p1, by simp [leaf000], leaf000p3, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p1, leaf000p2, leaf000p3]
        · refine ⟨leaf000p2, by simp [leaf000], leaf000p0, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p2, leaf000p3, leaf000p0]
    · intro v hv
      simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      all_goals norm_num [leaf000, point, leaf000p0, leaf000p1, leaf000p2, leaf000p3, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005
