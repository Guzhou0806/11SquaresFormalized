import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf002p0 : QPoint := ((27879205527889942497298934014370919727/13653690217200000000000000000000000000), (66047/131074))
def leaf002p1 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf002p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf002p3 : QPoint := ((15545978537846986399300899888381104373/14062195445600000000000000000000000000), (66047/131074))

def leaf002 : WallOwnershipLeaf where
  margin := (66047/131074)
  polygon := [baselineEdge leaf002p0 leaf002p1, baselineEdge leaf002p1 leaf002p2, baselineEdge leaf002p2 leaf002p3, baselineEdge leaf002p3 leaf002p0]
  vertices := [leaf002p0, leaf002p1, leaf002p2, leaf002p3]
  implications := [[(10, (470428252531874175282840182189372208555017/476751561789180773135700000000000000000000))], [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))], [(8, (3822130146346366054606357249854052703901139/4024531257922114266047200000000000000000000))], [(2, (6858067272008092185060607384892351481267847/7324139813690858400000000000000000000000000))]]

theorem leaf002_checked : leaf002.Check 1 [point] (1/256) (3/512) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf002, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf002, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf002p0, leaf002p1, leaf002p2, leaf002p3]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf002]
      · intro v hv
        simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · refine ⟨leaf002p3, by simp [leaf002], leaf002p1, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p3, leaf002p0, leaf002p1]
        · refine ⟨leaf002p0, by simp [leaf002], leaf002p2, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p0, leaf002p1, leaf002p2]
        · refine ⟨leaf002p1, by simp [leaf002], leaf002p3, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p1, leaf002p2, leaf002p3]
        · refine ⟨leaf002p2, by simp [leaf002], leaf002p0, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p2, leaf002p3, leaf002p0]
    · intro v hv
      simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      all_goals norm_num [leaf002, point, leaf002p0, leaf002p1, leaf002p2, leaf002p3, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005
