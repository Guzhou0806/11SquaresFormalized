import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf007p0 : QPoint := ((5231401505535037415698119892124735517/4478694562400000000000000000000000000), (29047/41746))
def leaf007p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf007p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf007p3 : QPoint := ((29047/41746), (117835515895682928831890824936841717/93045050275000000000000000000000000))
def leaf007p4 : QPoint := ((29047/41746), (29047/41746))

def leaf007 : WallOwnershipLeaf where
  margin := (29047/41746)
  polygon := [baselineEdge leaf007p0 leaf007p1, baselineEdge leaf007p1 leaf007p2, baselineEdge leaf007p2 leaf007p3, baselineEdge leaf007p3 leaf007p4, baselineEdge leaf007p4 leaf007p0]
  vertices := [leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4]
  implications := [[(9, (758742931933725580337801469035867404497131/1281780382785423365048800000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (1742496541116433370610320228878123213709/2314980521682168738300000000000000000000))], [(0, (53094473033182928831890824936841717/93045050275000000000000000000000000))], [(2, (2115111538735037415698119892124735517/4478694562400000000000000000000000000))]]

theorem leaf007_checked : leaf007.Check 0 [point] (207/512) (67/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf007, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf007, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf007]
      · intro v hv
        simp only [leaf007, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf007p4, by simp [leaf007], leaf007p1, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p4, leaf007p0, leaf007p1]
        · refine ⟨leaf007p0, by simp [leaf007], leaf007p2, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p0, leaf007p1, leaf007p2]
        · refine ⟨leaf007p1, by simp [leaf007], leaf007p3, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p1, leaf007p2, leaf007p3]
        · refine ⟨leaf007p2, by simp [leaf007], leaf007p4, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p2, leaf007p3, leaf007p4]
        · refine ⟨leaf007p3, by simp [leaf007], leaf007p0, by simp [leaf007],
            by simp [leaf007], by simp [leaf007], ?_⟩
          norm_num [leaf007p3, leaf007p4, leaf007p0]
    · intro v hv
      simp only [leaf007, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf007, point, leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
