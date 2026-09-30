import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf001p0 : QPoint := ((22310703534613034395698396500289194659/10922827172400000000000000000000000000), (263167/524290))
def leaf001p1 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf001p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf001p3 : QPoint := ((12429521549706257685413535563848405041/11249627615200000000000000000000000000), (263167/524290))

def leaf001 : WallOwnershipLeaf where
  margin := (263167/524290)
  polygon := [baselineEdge leaf001p0 leaf001p1, baselineEdge leaf001p1 leaf001p2, baselineEdge leaf001p2 leaf001p3, baselineEdge leaf001p3 leaf001p0]
  vertices := [leaf001p0, leaf001p1, leaf001p2, leaf001p3]
  implications := [[(10, (377760099706708336856188533378192403105589/381396884707035090936900000000000000000000))], [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))], [(8, (3069322721677266289611009113212355298729463/3219588161215779313282400000000000000000000))], [(2, (5494172637016735589996224797938890944220699/5859244797473152800000000000000000000000000))]]

theorem leaf001_checked : leaf001.Check 1 [point] (1/512) (1/256) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf001, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf001, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf001p0, leaf001p1, leaf001p2, leaf001p3]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf001]
      · intro v hv
        simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · refine ⟨leaf001p3, by simp [leaf001], leaf001p1, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p3, leaf001p0, leaf001p1]
        · refine ⟨leaf001p0, by simp [leaf001], leaf001p2, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p0, leaf001p1, leaf001p2]
        · refine ⟨leaf001p1, by simp [leaf001], leaf001p3, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p1, leaf001p2, leaf001p3]
        · refine ⟨leaf001p2, by simp [leaf001], leaf001p0, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p2, leaf001p3, leaf001p0]
    · intro v hv
      simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      all_goals norm_num [leaf001, point, leaf001p0, leaf001p1, leaf001p2, leaf001p3, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell01Point005
