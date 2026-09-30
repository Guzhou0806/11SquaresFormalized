import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf014p0 : QPoint := ((94456537697003469614924749774775169081/84795229503200000000000000000000000000), (2093431/3951890))
def leaf014p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf014p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf014p3 : QPoint := ((2093431/3951890), (2228903742941123986113452939968645681/1761624125575000000000000000000000000))
def leaf014p4 : QPoint := ((2093431/3951890), (2093431/3951890))

def leaf014 : WallOwnershipLeaf where
  margin := (2093431/3951890)
  polygon := [baselineEdge leaf014p0 leaf014p1, baselineEdge leaf014p1 leaf014p2, baselineEdge leaf014p2 leaf014p3, baselineEdge leaf014p3 leaf014p4, baselineEdge leaf014p4 leaf014p0]
  vertices := [leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4]
  implications := [[(9, (21878567591822244953819547968515086653371183/24267978138867851971938400000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (46598268614889667168980110234758618056937/43829580672785636061900000000000000000000))], [(0, (1295720239648623986113452939968645681/1761624125575000000000000000000000000))], [(2, (49538039941723469614924749774775169081/84795229503200000000000000000000000000))]]

theorem leaf014_checked : leaf014.Check 0 [point] (451/512) (963/1024) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf014, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf014, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf014]
      · intro v hv
        simp only [leaf014, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf014p4, by simp [leaf014], leaf014p1, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p4, leaf014p0, leaf014p1]
        · refine ⟨leaf014p0, by simp [leaf014], leaf014p2, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p0, leaf014p1, leaf014p2]
        · refine ⟨leaf014p1, by simp [leaf014], leaf014p3, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p1, leaf014p2, leaf014p3]
        · refine ⟨leaf014p2, by simp [leaf014], leaf014p4, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p2, leaf014p3, leaf014p4]
        · refine ⟨leaf014p3, by simp [leaf014], leaf014p0, by simp [leaf014],
            by simp [leaf014], by simp [leaf014], ?_⟩
          norm_num [leaf014p3, leaf014p4, leaf014p0]
    · intro v hv
      simp only [leaf014, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf014, point, leaf014p0, leaf014p1, leaf014p2, leaf014p3, leaf014p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
