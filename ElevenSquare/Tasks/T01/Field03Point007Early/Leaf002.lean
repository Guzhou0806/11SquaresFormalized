import ElevenSquare.Tasks.T01.Field03Point007Early.Data

namespace ElevenSquare.Tasks.T01.Field03Point007Early
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf002p0 : QPoint := ((62220554563615707547430135777328404637/56249854626400000000000000000000000000), (265207/524306))
def leaf002p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf002p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf002p3 : QPoint := ((265207/524306), (1478369490319981164282406718232542837/1168592874275000000000000000000000000))
def leaf002p4 : QPoint := ((265207/524306), (265207/524306))

def leaf002 : WallOwnershipLeaf where
  margin := (265207/524306)
  polygon := [baselineEdge leaf002p0 leaf002p1, baselineEdge leaf002p1 leaf002p2, baselineEdge leaf002p2 leaf002p3, baselineEdge leaf002p3 leaf002p4, baselineEdge leaf002p4 leaf002p0]
  vertices := [leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4]
  implications := [[(9, (15230774049682723902376068055006934685533291/16098432074371057893816800000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (32210756205363090183759271736745395239949/29074837766518736226300000000000000000000))], [(0, (887266183457481164282406718232542837/1168592874275000000000000000000000000))], [(2, (33767980692815707547430135777328404637/56249854626400000000000000000000000000))]]

theorem leaf002_checked : leaf002.Check 0 [point] (3/512) (3/256) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf002, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf002, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf002]
      · intro v hv
        simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf002p4, by simp [leaf002], leaf002p1, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p4, leaf002p0, leaf002p1]
        · refine ⟨leaf002p0, by simp [leaf002], leaf002p2, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p0, leaf002p1, leaf002p2]
        · refine ⟨leaf002p1, by simp [leaf002], leaf002p3, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p1, leaf002p2, leaf002p3]
        · refine ⟨leaf002p2, by simp [leaf002], leaf002p4, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p2, leaf002p3, leaf002p4]
        · refine ⟨leaf002p3, by simp [leaf002], leaf002p0, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p3, leaf002p4, leaf002p0]
    · intro v hv
      simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf002, point, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007Early
