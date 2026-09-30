import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf003p0 : QPoint := ((258236298847630890276384857300959165053/227540985941600000000000000000000000000), (1259927/2120914))
def leaf003p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf003p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf003p3 : QPoint := ((1259927/2120914), (5983239374913478257091958441050560853/4727172657475000000000000000000000000))
def leaf003p4 : QPoint := ((1259927/2120914), (1259927/2120914))

def leaf003 : WallOwnershipLeaf where
  margin := (1259927/2120914)
  polygon := [baselineEdge leaf003p0 leaf003p1, baselineEdge leaf003p1 leaf003p2, baselineEdge leaf003p2 leaf003p3, baselineEdge leaf003p3 leaf003p4, baselineEdge leaf003p4 leaf003p0]
  vertices := [leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4]
  implications := [[(9, (50900939908587675688568194914452586603306379/65121112412565596963999200000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (110900562934225859881057268191223490099181/117613055099003862104700000000000000000000))], [(0, (3175066830050978257091958441050560853/4727172657475000000000000000000000000))], [(2, (123065786608830890276384857300959165053/227540985941600000000000000000000000000))]]

theorem leaf003_checked : leaf003.Check 0 [point] (109/1024) (85/512) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf003, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf003, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf003]
      · intro v hv
        simp only [leaf003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf003p4, by simp [leaf003], leaf003p1, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p4, leaf003p0, leaf003p1]
        · refine ⟨leaf003p0, by simp [leaf003], leaf003p2, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p0, leaf003p1, leaf003p2]
        · refine ⟨leaf003p1, by simp [leaf003], leaf003p3, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p1, leaf003p2, leaf003p3]
        · refine ⟨leaf003p2, by simp [leaf003], leaf003p4, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p2, leaf003p3, leaf003p4]
        · refine ⟨leaf003p3, by simp [leaf003], leaf003p0, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p3, leaf003p4, leaf003p0]
    · intro v hv
      simp only [leaf003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf003, point, leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
