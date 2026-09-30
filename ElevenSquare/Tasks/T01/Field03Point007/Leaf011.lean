import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf011p0 : QPoint := ((18393672487824397386224770145591148033/15894612997600000000000000000000000000), (490799/740770))
def leaf011p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf011p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf011p3 : QPoint := ((490799/740770), (418113017691173492985195067256571833/330211190975000000000000000000000000))
def leaf011p4 : QPoint := ((490799/740770), (490799/740770))

def leaf011 : WallOwnershipLeaf where
  margin := (490799/740770)
  polygon := [baselineEdge leaf011p0 leaf011p1, baselineEdge leaf011p1 leaf011p2, baselineEdge leaf011p2 leaf011p3, baselineEdge leaf011p3 leaf011p4, baselineEdge leaf011p4 leaf011p0]
  vertices := [leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4]
  implications := [[(9, (2974704577610400322297864198810422542180519/4548960159804331270671200000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (6694703378994116153629123345690831854641/8215724242066306406700000000000000000000))], [(0, (199330774458673492985195067256571833/330211190975000000000000000000000000))], [(2, (7862657240704397386224770145591148033/15894612997600000000000000000000000000))]]

theorem leaf011_checked : leaf011.Check 0 [point] (1255/2048) (329/512) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf011, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf011, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf011]
      · intro v hv
        simp only [leaf011, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf011p4, by simp [leaf011], leaf011p1, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p4, leaf011p0, leaf011p1]
        · refine ⟨leaf011p0, by simp [leaf011], leaf011p2, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p0, leaf011p1, leaf011p2]
        · refine ⟨leaf011p1, by simp [leaf011], leaf011p3, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p1, leaf011p2, leaf011p3]
        · refine ⟨leaf011p2, by simp [leaf011], leaf011p4, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p2, leaf011p3, leaf011p4]
        · refine ⟨leaf011p3, by simp [leaf011], leaf011p0, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p3, leaf011p4, leaf011p0]
    · intro v hv
      simp only [leaf011, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf011, point, leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
